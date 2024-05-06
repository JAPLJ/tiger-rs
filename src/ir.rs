use anyhow::{bail, Result};
use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    types::{BasicMetadataTypeEnum, BasicType},
    values::{
        BasicMetadataValueEnum, BasicValueEnum as Val, FunctionValue, IntValue, PointerValue,
    },
    AddressSpace, IntPredicate,
};
use itertools::Itertools;
use lasso::Key;
use rpds::HashTrieMap;

use crate::{
    absyn::{BinOp, Symbol},
    symtable::SymTable,
    typing::{self, Decl, Expr, Func, Type, VEnv, Var},
};

#[derive(Debug, Clone)]
enum EnvEntry<'ctx> {
    Var(Type, PointerValue<'ctx>),
    Func(FunctionValue<'ctx>, Vec<bool>),
}

type Env<'ctx> = HashTrieMap<Symbol, EnvEntry<'ctx>>;

pub fn gen_ir<'a, 'ctx>(
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    ext_fs: VEnv,
    symt: &SymTable,
    e: &Expr,
) -> Result<()> {
    let mut irgen = IRGen::from_ctx(ctx, builder, module);
    irgen.gen_ext_func(ext_fs, symt)?;
    match e {
        Expr::Let(decls, body) => {
            if let [Decl::Func(fs)] = &decls[..] {
                irgen.gen_func(fs)?;
                irgen.gen_main(body)?;
            } else {
                panic!("unexpected error: lambda lifted")
            }
        }
        _ => panic!("unexpected error: lambda lifted"),
    }
    Ok(())
}

macro_rules! ensure_int {
    ($e:expr) => {{
        use inkwell::values::BasicValueEnum;
        match $e {
            BasicValueEnum::IntValue(v) => v,
            _ => panic!("unexpected error: int expected"),
        }
    }};
}

struct IRGen<'a, 'ctx> {
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    env: Env<'ctx>,
    cur_func: Option<FunctionValue<'ctx>>,
    cur_block: Vec<BasicBlock<'ctx>>,
}

impl<'a, 'ctx> IRGen<'a, 'ctx> {
    fn from_ctx(ctx: &'ctx Context, builder: &'a Builder<'ctx>, module: &'a Module<'ctx>) -> Self {
        IRGen {
            ctx,
            builder,
            module,
            env: Env::new(),
            cur_func: None,
            cur_block: vec![],
        }
    }

    fn create_entry_block_alloca<T: BasicType<'ctx>>(
        &self,
        ty: T,
        name: &str,
    ) -> PointerValue<'ctx> {
        let b = self.ctx.create_builder();
        let entry = self.cur_func().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(instr) => b.position_before(&instr),
            None => b.position_at_end(entry),
        }

        b.build_alloca(ty, name).unwrap()
    }

    fn create_entry_block_array_alloca<T: BasicType<'ctx>>(
        &self,
        ty: T,
        size: IntValue<'ctx>,
        name: &str,
    ) -> PointerValue<'ctx> {
        let b = self.ctx.create_builder();
        let entry = self.cur_func().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(instr) => b.position_before(&instr),
            None => b.position_at_end(entry),
        }

        b.build_array_alloca(ty, size, name).unwrap()
    }

    fn cur_func(&self) -> FunctionValue<'ctx> {
        self.cur_func.unwrap()
    }

    fn cur_block(&self) -> BasicBlock<'ctx> {
        *self.cur_block.last().unwrap()
    }

    fn unit(&self) -> Val<'ctx> {
        Val::PointerValue(self.ctx.ptr_type(AddressSpace::default()).const_null())
    }

    fn gen_ext_func(&mut self, ext_fs: VEnv, symt: &SymTable) -> Result<()> {
        for (nm, entry) in ext_fs.iter() {
            if let typing::EnvEntry::Func(args, ret) = entry {
                let name = symt.resolve(nm);
                let ret_type = ret.as_llvm_type(self.ctx);
                let arg_types = args
                    .iter()
                    .map(|a| a.as_llvm_type(self.ctx).into())
                    .collect_vec();
                let fn_type = ret_type.fn_type(&arg_types[..], false);
                let fv = self.module.add_function(name, fn_type, None);
                self.env
                    .insert_mut(*nm, EnvEntry::Func(fv, vec![false; args.len()]));
            }
        }
        Ok(())
    }

    fn gen_main(&mut self, e: &Expr) -> Result<()> {
        let i32_type = self.ctx.i32_type();
        let main_type = i32_type.fn_type(&[], false);
        let fv = self.module.add_function("main", main_type, None);
        let entry = self.ctx.append_basic_block(fv, "entry");
        self.cur_func = Some(fv);
        self.builder.position_at_end(entry);
        self.gen_exp(e)?;
        self.builder.build_return(Some(&i32_type.const_zero()))?;
        Ok(())
    }

    fn gen_exp(&mut self, e: &Expr) -> Result<Val<'ctx>> {
        match e {
            Expr::Var(v) => self.gen_var(v),
            Expr::Nil => Ok(self.unit()),
            Expr::Int(x) => Ok(Val::IntValue(
                self.ctx.i64_type().const_int(*x as u64, false),
            )),
            Expr::Str(s) => {
                let bytes = s.as_bytes();
                let i8_type = self.ctx.i8_type();
                let arr_type = i8_type.array_type((bytes.len() + 1) as u32);
                let g = self.module.add_global(arr_type, None, "str_const");
                g.set_constant(true);
                g.set_linkage(Linkage::Private);
                let mut arr_val = Vec::with_capacity(bytes.len() + 1);
                for b in [bytes, &[0]].concat() {
                    arr_val.push(i8_type.const_int(b.into(), false));
                }
                g.set_initializer(&i8_type.const_array(&arr_val[..]));
                Ok(Val::PointerValue(g.as_pointer_value()))
            }
            Expr::Call(f, args) => {
                let entry = self.env.get(f).unwrap().clone();
                if let EnvEntry::Func(fv, rf) = entry {
                    let mut targs = Vec::with_capacity(args.len());
                    for (a, r) in args.iter().zip(rf) {
                        if r {
                            let mut ok = false;
                            if let Expr::Var(v) = a {
                                if let Var::Simple(x) = v.as_ref() {
                                    if let EnvEntry::Var(_, p) = self.env.get(x).unwrap() {
                                        ok = true;
                                        targs.push(BasicMetadataValueEnum::from(*p));
                                    }
                                }
                            }
                            if !ok {
                                panic!("unexpected error: ref to simple var")
                            }
                        } else {
                            targs.push(self.gen_exp(a)?.into());
                        }
                    }
                    match self
                        .builder
                        .build_call(fv, &targs[..], "tmp_call")?
                        .try_as_basic_value()
                        .left()
                    {
                        Some(v) => Ok(v),
                        None => bail!("invalid call"),
                    }
                } else {
                    panic!("unexpected error: function not found")
                }
            }
            Expr::BinOp(lhs, op, rhs) => {
                let lhs = ensure_int!(self.gen_exp(lhs)?);
                let rhs = ensure_int!(self.gen_exp(rhs)?);

                let is_bool = match op {
                    BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => true,
                    _ => false,
                };
                let res = match op {
                    BinOp::Add => self.builder.build_int_add(lhs, rhs, "tmp_add")?,
                    BinOp::Sub => self.builder.build_int_sub(lhs, rhs, "tmp_sub")?,
                    BinOp::Mul => self.builder.build_int_mul(lhs, rhs, "tmp_mul")?,
                    BinOp::Div => self.builder.build_int_signed_div(lhs, rhs, "tmp_div")?,
                    BinOp::Eq => {
                        self.builder
                            .build_int_compare(IntPredicate::EQ, lhs, rhs, "tmp_eq")?
                    }
                    BinOp::Neq => {
                        self.builder
                            .build_int_compare(IntPredicate::NE, lhs, rhs, "tmp_neq")?
                    }
                    BinOp::Lt => {
                        self.builder
                            .build_int_compare(IntPredicate::SLT, lhs, rhs, "tmp_lt")?
                    }
                    BinOp::Le => {
                        self.builder
                            .build_int_compare(IntPredicate::SLE, lhs, rhs, "tmp_le")?
                    }
                    BinOp::Gt => {
                        self.builder
                            .build_int_compare(IntPredicate::SGT, lhs, rhs, "tmp_gt")?
                    }
                    BinOp::Ge => {
                        self.builder
                            .build_int_compare(IntPredicate::SGE, lhs, rhs, "tmp_ge")?
                    }
                };

                let res = if is_bool {
                    self.builder
                        .build_int_z_extend(res, self.ctx.i64_type(), "tmp_cast")?
                } else {
                    res
                };

                Ok(Val::IntValue(res))
            }
            Expr::Seq(es) => es
                .iter()
                .map(|e| self.gen_exp(e))
                .last()
                .unwrap_or(Ok(self.unit())),
            Expr::Assign(v, e) => {
                let ptr = self.gen_var_ref(v)?.1;
                let val = self.gen_exp(e)?;
                self.builder.build_store(ptr, val)?;
                Ok(self.unit())
            }
            Expr::If(cond, th, el) => {
                let par = self.cur_func();

                let cond = ensure_int!(self.gen_exp(cond)?);
                let cond = self.builder.build_int_compare(
                    IntPredicate::NE,
                    cond,
                    self.ctx.i64_type().const_int(0, false),
                    "cond_v",
                )?;

                let th_bb = self.ctx.append_basic_block(par, "then");
                let el_bb = self.ctx.append_basic_block(par, "el");
                let cont_bb = self.ctx.append_basic_block(par, "cont");
                self.builder.build_conditional_branch(cond, th_bb, el_bb)?;

                self.builder.position_at_end(th_bb);
                let then_val = self.gen_exp(th)?;
                self.builder.build_unconditional_branch(cont_bb)?;
                let then_bb = self.builder.get_insert_block().unwrap();

                self.builder.position_at_end(el_bb);
                if let Some(el) = el {
                    let else_val = self.gen_exp(el)?;
                    self.builder.build_unconditional_branch(cont_bb)?;
                    let else_bb = self.builder.get_insert_block().unwrap();

                    self.builder.position_at_end(cont_bb);
                    let phi = self.builder.build_phi(then_val.get_type(), "iftmp")?;
                    phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);
                    Ok(phi.as_basic_value())
                } else {
                    self.builder.position_at_end(cont_bb);
                    Ok(self.unit())
                }
            }
            Expr::While(cond, body) => {
                let par = self.cur_func();

                let loop_bb = self.ctx.append_basic_block(par, "loop");
                let after_bb = self.ctx.append_basic_block(par, "after");
                self.cur_block.push(after_bb);

                self.builder.position_at_end(loop_bb);
                self.gen_exp(body)?;

                let cond = ensure_int!(self.gen_exp(cond)?);
                let cond = self.builder.build_int_compare(
                    IntPredicate::NE,
                    cond,
                    self.ctx.i64_type().const_int(0, false),
                    "cond_v",
                )?;
                self.builder
                    .build_conditional_branch(cond, loop_bb, after_bb)?;

                self.builder.position_at_end(after_bb);
                self.cur_block.pop();
                Ok(self.unit())
            }
            Expr::Break => {
                self.builder.build_unconditional_branch(self.cur_block())?;
                Ok(self.unit())
            }
            Expr::Let(decls, e) => {
                for d in decls {
                    if let Decl::Var(nm, ty, e) = d {
                        let v = self.create_entry_block_alloca(ty.as_llvm_type(self.ctx), "var");
                        let e = self.gen_exp(e)?;
                        self.builder.build_store(v, e)?;
                        self.env.insert_mut(*nm, EnvEntry::Var(ty.clone(), v));
                    } else {
                        panic!("unexpected error: lambda lifted")
                    }
                }
                let r = self.gen_exp(e);
                for d in decls {
                    if let Decl::Var(nm, _, _) = d {
                        self.env.remove_mut(nm);
                    }
                }
                r
            }
            Expr::Array(ty, size, init) => {
                if let Type::Array(ety) = ty {
                    let size = ensure_int!(self.gen_exp(size)?);
                    let init = self.gen_exp(init)?;
                    let ety = ety.as_llvm_type(self.ctx);
                    let arr = self.create_entry_block_array_alloca(ety, size, "arr");

                    let i64_type = self.ctx.i64_type();
                    let p = self.create_entry_block_alloca(i64_type, "init_counter_p");
                    self.builder.build_store(p, i64_type.const_zero())?;

                    let par = self.cur_func();
                    let loop_bb = self.ctx.append_basic_block(par, "init_loop");
                    let after_bb = self.ctx.append_basic_block(par, "after");
                    self.builder.position_at_end(loop_bb);
                    let pi = ensure_int!(self.builder.build_load(i64_type, p, "init_counter")?);
                    let arr_i = unsafe {
                        self.builder
                            .build_gep(ety, arr, &[i64_type.const_zero(), pi], "arr_i")?
                    };
                    self.builder.build_store(arr_i, init)?;
                    let pi = self.builder.build_int_add(
                        pi,
                        i64_type.const_int(1, false),
                        "next_loop",
                    )?;
                    self.builder.build_store(p, pi)?;
                    let cond =
                        self.builder
                            .build_int_compare(IntPredicate::NE, pi, size, "cond")?;
                    self.builder
                        .build_conditional_branch(cond, loop_bb, after_bb)?;

                    self.builder.position_at_end(after_bb);
                    Ok(Val::PointerValue(arr))
                } else {
                    panic!("unexpected error: array required")
                }
            }
        }
    }

    fn gen_var(&mut self, v: &Var) -> Result<Val<'ctx>> {
        let (ty, ptr) = self.gen_var_ref(v)?;
        let ty = ty.as_llvm_type(self.ctx);
        let val = self.builder.build_load(ty, ptr, "var")?;
        Ok(val)
    }

    fn gen_var_ref(&mut self, v: &Var) -> Result<(Type, PointerValue<'ctx>)> {
        match v {
            Var::Simple(x) => {
                let entry = self.env.get(x).unwrap().clone();
                if let EnvEntry::Var(ty, ptr) = entry {
                    Ok((ty, ptr))
                } else {
                    panic!("unexpected error: undefined variable")
                }
            }
            Var::Subscript(arr, ix) => {
                let (ty, arr) = self.gen_var_ref(arr)?;
                if let Type::Array(ety) = ty {
                    let ix = ensure_int!(self.gen_exp(ix)?);
                    let ptr = unsafe {
                        self.builder.build_gep(
                            ety.as_llvm_type(self.ctx),
                            arr,
                            &[self.ctx.i64_type().const_zero(), ix],
                            "arr_subscript",
                        )?
                    };
                    Ok((*ety, ptr))
                } else {
                    panic!("unexpected error: array required")
                }
            }
        }
    }

    fn gen_func(&mut self, fs: &Vec<Func>) -> Result<()> {
        let mut funcs = Vec::with_capacity(fs.len());
        for f in fs {
            let result_type = f.result.as_llvm_type(self.ctx);
            let mut arg_types = Vec::with_capacity(f.args.len());
            let mut arg_refs = Vec::with_capacity(f.args.len());
            for (_, ty, rf) in &f.args {
                arg_types.push(if *rf {
                    BasicMetadataTypeEnum::PointerType(self.ctx.ptr_type(AddressSpace::default()))
                } else {
                    ty.as_llvm_type(self.ctx).into()
                });
                arg_refs.push(*rf);
            }
            let fn_type = result_type.fn_type(&arg_types[..], false);
            let func = self
                .module
                .add_function(&format!("f{}", f.id.into_usize()), fn_type, None);
            funcs.push(func);
            self.env.insert_mut(f.id, EnvEntry::Func(func, arg_refs));
        }

        for (f, fv) in fs.iter().zip(funcs) {
            let entry = self.ctx.append_basic_block(fv, "entry");
            self.builder.position_at_end(entry);
            self.cur_func = Some(fv);

            for (i, arg) in fv.get_param_iter().enumerate() {
                let (nm, ty, rf) = &f.args[i];
                if *rf {
                    // call-by-reference
                    self.env
                        .insert_mut(*nm, EnvEntry::Var(ty.clone(), arg.into_pointer_value()));
                } else {
                    // call-by-value
                    let ptr = self.create_entry_block_alloca(ty.as_llvm_type(self.ctx), "arg");
                    self.builder.build_store(ptr, arg)?;
                    self.env.insert_mut(*nm, EnvEntry::Var(ty.clone(), ptr));
                }
            }

            let body = self.gen_exp(&f.body)?;
            self.builder.build_return(Some(&body))?;
            for (nm, _, _) in &f.args {
                self.env.remove_mut(nm);
            }
        }
        Ok(())
    }
}
