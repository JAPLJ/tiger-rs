// Type Checker
use crate::{
    absyn::{BinOp, Decl as EDecl, Expr as EExpr, Spanned, Symbol, Var as EVar},
    error::GenericError,
    symtable::SymTable,
    typing::{self, Decl as TDecl, EnvEntry, Expr as TExpr, TEnv, Type, VEnv, Var as TVar},
};

pub type ExpTy = (TExpr, Type);
pub type Error = GenericError;

macro_rules! check_type {
    ($t:expr, $exp_t:expr, $span:expr, $errs:ident) => {{
        if $t != $exp_t {
            $errs.push(crate::error::GenericError(
                format!("mismatched types"),
                format!("expected {:?}, found {:?}", $exp_t, $t),
                $span,
            ));
        }
    }};
}

macro_rules! undefined_symbol {
    ($sym:expr, $kind:expr, $span:expr, $errs:ident) => {{
        $errs.push(crate::error::GenericError(
            format!("cannot find {}", $kind),
            format!("{} is not defined here", $sym),
            $span,
        ));
    }};
}

macro_rules! trans_expect {
    ($symt:expr, $venv:expr, $tenv:expr, $e:expr, $errs:ident, $exp_t:expr) => {{
        let (te, et) = inner($symt, $venv, $tenv, $e, $errs);
        check_type!(et, $exp_t, (*$e).1, $errs);
        te
    }};
}

pub fn trans_exp(
    symt: &mut SymTable,
    venv: &VEnv,
    tenv: &TEnv,
    e: &Spanned<EExpr>,
) -> (ExpTy, Vec<Error>) {
    let mut errs = vec![];
    (inner(symt, venv, tenv, e, &mut errs), errs)
}

fn inner(
    symt: &mut SymTable,
    venv: &VEnv,
    tenv: &TEnv,
    e: &Spanned<EExpr>,
    errs: &mut Vec<Error>,
) -> ExpTy {
    let (e, span) = e;
    match e {
        EExpr::Var(v) => {
            let (tv, vt) = trans_var(symt, venv, tenv, &(v.as_ref().clone(), *span), errs);
            (TExpr::Var(Box::new(tv)), vt)
        }
        EExpr::Nil => unimplemented!(),
        EExpr::Int(x) => (TExpr::Int(*x), Type::Int),
        EExpr::Str(s) => (TExpr::Str(s.to_string()), Type::String),
        EExpr::Call(f, args) => {
            if let Some(ft) = venv.get(f) {
                if let EnvEntry::Func(aty, rty) = ft {
                    if args.len() != aty.len() {
                        errs.push(GenericError(
                            format!("unexpected number of arguments"),
                            format!("expected {} arguments, found {}", aty.len(), args.len()),
                            *span,
                        ));
                        (TExpr::Int(0), rty.clone())
                    } else {
                        let mut targs = vec![];
                        for (a, ty) in args.iter().zip(aty) {
                            targs.push(trans_expect!(symt, venv, tenv, a, errs, *ty));
                        }
                        (TExpr::Call(f.clone(), targs), rty.clone())
                    }
                } else {
                    errs.push(GenericError(
                        format!("call expression requires function"),
                        format!("{} has type {:?}", symt.resolve(f), ft),
                        *span,
                    ));
                    (TExpr::Int(0), Type::Int)
                }
            } else {
                undefined_symbol!(symt.resolve(f), "function", *span, errs);
                (TExpr::Int(0), Type::Int)
            }
        }
        EExpr::BinOp(lhs, op, rhs) => {
            let lhs = trans_expect!(symt, venv, tenv, lhs, errs, Type::Int);
            let rhs = trans_expect!(symt, venv, tenv, rhs, errs, Type::Int);
            (TExpr::BinOp(Box::new(lhs), *op, Box::new(rhs)), Type::Int)
        }
        EExpr::Seq(es) => {
            let mut es2 = vec![];
            let mut last_type = Type::Unit;
            for e in es {
                let (te, tt) = inner(symt, venv, tenv, e, errs);
                es2.push(te);
                last_type = tt;
            }
            (TExpr::Seq(es2), last_type)
        }
        EExpr::Assign(v, x) => {
            let (tv, vt) = trans_var(symt, venv, tenv, v, errs);
            let tx = trans_expect!(symt, venv, tenv, x, errs, vt);
            (TExpr::Assign(Box::new(tv), Box::new(tx)), Type::Unit)
        }
        EExpr::If(cond, th, el) => {
            let cond = trans_expect!(symt, venv, tenv, cond, errs, Type::Int);
            let (th, tt) = inner(symt, venv, tenv, th, errs);
            if let Some(el) = el {
                let el = trans_expect!(symt, venv, tenv, el, errs, tt);
                (
                    TExpr::If(Box::new(cond), Box::new(th), Some(Box::new(el))),
                    tt,
                )
            } else {
                (TExpr::If(Box::new(cond), Box::new(th), None), Type::Unit)
            }
        }
        EExpr::While(cond, body) => {
            let cond = trans_expect!(symt, venv, tenv, cond, errs, Type::Int);
            let (body, _) = inner(symt, venv, tenv, body, errs);
            (TExpr::While(Box::new(cond), Box::new(body)), Type::Unit)
        }
        EExpr::For(v, fr, to, body) => {
            let fr = trans_expect!(symt, venv, tenv, fr, errs, Type::Int);
            let to = trans_expect!(symt, venv, tenv, to, errs, Type::Int);
            let venv2 = venv.insert(*v, EnvEntry::Var(Type::Int));
            let (body, _) = inner(symt, &venv2, tenv, body, errs);

            // convert for-loop to while-loop
            // for v := f to t do body
            // =>
            // let v := f, t := t in
            //   while v != t do { body; v := v + 1 }
            let tv = symt.new_sym();
            fn simple_ref(x: Symbol) -> Box<TExpr> {
                Box::new(TExpr::Var(Box::new(TVar::Simple(x))))
            }
            (
                TExpr::Let(
                    vec![TDecl::Var(*v, Type::Int, fr), TDecl::Var(tv, Type::Int, to)],
                    Box::new(TExpr::While(
                        Box::new(TExpr::BinOp(simple_ref(*v), BinOp::Neq, simple_ref(tv))),
                        Box::new(TExpr::Seq(vec![
                            body,
                            TExpr::Assign(
                                Box::new(TVar::Simple(*v)),
                                Box::new(TExpr::BinOp(
                                    simple_ref(*v),
                                    BinOp::Add,
                                    Box::new(TExpr::Int(1)),
                                )),
                            ),
                        ])),
                    )),
                ),
                Type::Unit,
            )
        }
        EExpr::Break => {
            // TODO: check if inside a loop
            (TExpr::Break, Type::Unit)
        }
        EExpr::Let(decls, e2) => {
            let mut tdecls = vec![];
            let (venv2, tenv2) =
                decls
                    .iter()
                    .fold((venv.clone(), tenv.clone()), |(ve, te), decl| {
                        let (td, ve, te) = trans_dec(symt, &ve, &te, decl, errs);
                        tdecls.push(td);
                        (ve, te)
                    });
            let (e2, t) = inner(symt, &venv2, &tenv2, e2, errs);
            (TExpr::Let(tdecls, Box::new(e2)), t)
        }
        EExpr::Array(atys, size, init) => {
            if let Ok(aty) = atys.resolve(tenv) {
                if let Type::Array(ref ety) = aty {
                    let size = trans_expect!(symt, venv, tenv, size, errs, Type::Int);
                    let init = trans_expect!(symt, venv, tenv, init, errs, **ety);
                    (
                        TExpr::Array(aty.clone(), Box::new(size), Box::new(init)),
                        aty.clone(),
                    )
                } else {
                    if let Type::Name(nm, _) = atys {
                        errs.push(GenericError(
                            format!("cannot create array"),
                            format!("{} has type {:?}, not array", symt.resolve(nm), aty),
                            *span,
                        ));
                    }
                    (TExpr::Int(0), Type::Int)
                }
            } else {
                if let Type::Name(nm, _) = atys {
                    undefined_symbol!(symt.resolve(nm), "type", *span, errs);
                }
                (TExpr::Int(0), Type::Int)
            }
        }
    }
}

fn trans_var(
    symt: &mut SymTable,
    venv: &VEnv,
    tenv: &TEnv,
    v: &Spanned<EVar>,
    errs: &mut Vec<Error>,
) -> (TVar, Type) {
    let (v, span) = v;
    match v {
        EVar::Simple(s) => {
            if let Some(ee) = venv.get(s) {
                if let EnvEntry::Var(ty) = ee {
                    let ty = ty.resolve(tenv).unwrap_or_else(|nm| {
                        undefined_symbol!(symt.resolve(&nm), "type", *span, errs);
                        Type::Int
                    });
                    (TVar::Simple(*s), ty)
                } else {
                    errs.push(GenericError(
                        format!("function is not a variable"),
                        format!("{} is function, not variable", symt.resolve(s)),
                        *span,
                    ));
                    (TVar::Simple(*s), Type::Int)
                }
            } else {
                undefined_symbol!(symt.resolve(s), "variable", *span, errs);
                (TVar::Simple(*s), Type::Int)
            }
        }
        EVar::Subscript(arr, ix) => {
            let (arr, aty) = trans_var(symt, venv, tenv, arr, errs);
            if let Type::Array(ety) = aty {
                let ix = trans_expect!(symt, venv, tenv, ix, errs, Type::Int);
                (TVar::Subscript(Box::new(arr), ix), *ety)
            } else {
                errs.push(GenericError(
                    format!("subscript requires array"),
                    format!("this has type {:?}", aty),
                    *span,
                ));
                (TVar::Subscript(Box::new(arr), TExpr::Int(0)), Type::Int)
            }
        }
    }
}

fn trans_dec(
    symt: &mut SymTable,
    venv: &VEnv,
    tenv: &TEnv,
    d: &Spanned<EDecl>,
    errs: &mut Vec<Error>,
) -> (TDecl, VEnv, TEnv) {
    let (d, _span) = d;
    match d {
        EDecl::Var(v, ty, init) => {
            let (init, ity) = {
                let spec_ty = ty.as_ref().and_then(|(ty, tyspan)| {
                    ty.resolve(tenv)
                        .inspect_err(|nm| {
                            undefined_symbol!(symt.resolve(nm), "type", *tyspan, errs);
                        })
                        .ok()
                });
                if let Some(spec_ty) = spec_ty {
                    (
                        trans_expect!(symt, venv, tenv, init, errs, spec_ty),
                        spec_ty,
                    )
                } else {
                    inner(symt, venv, tenv, init, errs)
                }
            };
            (
                TDecl::Var(*v, ity.clone(), init),
                venv.insert(*v, EnvEntry::Var(ity)),
                tenv.clone(),
            )
        }
        EDecl::Func(fs) => {
            let ftypes = {
                let mut ftypes = vec![];
                for (f, sp) in fs {
                    let ret_ty = f.result.as_ref().map_or(Type::Unit, |t| {
                        t.resolve(tenv).unwrap_or_else(|nm| {
                            undefined_symbol!(symt.resolve(&nm), "type", *sp, errs);
                            Type::Int
                        })
                    });
                    let mut args_tys = vec![];
                    for (_, aty) in &f.args {
                        args_tys.push(aty.resolve(tenv).unwrap_or_else(|nm| {
                            undefined_symbol!(symt.resolve(&nm), "type", *sp, errs);
                            Type::Int
                        }));
                    }
                    ftypes.push((f, args_tys, ret_ty));
                }
                ftypes
            };

            let venv2 = ftypes
                .iter()
                .fold(venv.clone(), |env, (f, args_tys, ret_ty)| {
                    env.insert(f.id, EnvEntry::Func(args_tys.clone(), ret_ty.clone()))
                });

            let mut tfs = vec![];
            for (f, args_tys, ret_ty) in ftypes {
                let mut args = vec![];
                let venv3 = args_tys.iter().zip(f.args.iter()).fold(
                    venv2.clone(),
                    |env, (t, (argname, _))| {
                        args.push((*argname, t.clone()));
                        env.insert(*argname, EnvEntry::Var(t.clone()))
                    },
                );
                let body = trans_expect!(symt, &venv3, tenv, &f.body, errs, ret_ty);
                tfs.push(typing::Func {
                    id: f.id,
                    args,
                    result: ret_ty.clone(),
                    body,
                });
            }

            (TDecl::Func(tfs), venv2, tenv.clone())
        }
        EDecl::Type(ts) => {
            let mut tenv2 = tenv.clone();
            let mut done = 0;
            while done < ts.len() {
                let mut updated = false;
                for (nm, (t, _)) in ts {
                    if tenv2.contains_key(nm) {
                        continue;
                    }
                    if let Ok(t) = t.resolve(&tenv2) {
                        tenv2.insert_mut(*nm, t);
                        done += 1;
                        updated = true;
                    }
                }
                if !updated {
                    break;
                }
            }

            let mut tts = vec![];
            for (nm, (_, tspan)) in ts {
                if let Some(t) = tenv2.get(nm) {
                    tts.push((*nm, t.clone()));
                } else {
                    errs.push(GenericError(
                        format!("cannot resolve type"),
                        format!("{} does not resolve into type", symt.resolve(nm)),
                        *tspan,
                    ));
                }
            }
            (TDecl::Type(tts), venv.clone(), tenv2)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        parse,
        semant::trans_exp,
        symtable::SymTable,
        test_util::tokenize_ok,
        typing::{TEnv, Type, VEnv},
    };
    use chumsky::prelude::*;

    use super::{Error, ExpTy};

    fn typecheck(prog: &str) -> (ExpTy, Vec<Error>, SymTable) {
        let toks = tokenize_ok(prog);
        let (expr, symt, errs) = parse!(toks);
        assert!(errs.is_empty(), "parse error: {:?}", errs);
        let mut symt = SymTable::from_rodeo(symt.unwrap());

        let venv = VEnv::new();
        let tenv = TEnv::new()
            .insert(symt.get_or_intern("int"), Type::Int)
            .insert(symt.get_or_intern("string"), Type::String);

        let (expty, errs) = trans_exp(&mut symt, &venv, &tenv, &expr.unwrap());
        (expty, errs, symt)
    }

    fn type_ok(prog: &str) -> bool {
        typecheck(prog).1.is_empty()
    }

    fn type_fail(prog: &str) -> bool {
        !type_ok(prog)
    }

    #[test]
    fn type_primitive() {
        assert!(type_ok(r#"let var x: int := 0 in x end"#));
        assert!(type_ok(r#"let var x: string := "0" in x end"#));
        assert!(type_fail(r#"let var x: int := "0" in x end"#));
        assert!(type_fail(r#"let var x: string := 0 in x end"#));
    }

    #[test]
    fn type_array() {
        assert!(type_ok(
            r#"
        let 
            type t1 = int
            type t2 = array of t1
            var x := t2 [10] of 0
            var y: t1 := 5
        in
            x[y / 2] := x[y + 1] - 2
        end"#
        ));
        assert!(type_fail(r#"let var x := int [10] of 0 in x[0] end"#));
        assert!(type_fail(
            r#"
        let
            type t = array of int
            var x := t [10] of "0"
        in x[0] end"#
        ));
        assert!(type_fail(
            r#"
        let
            type t = array of int
            var x := t [10] of 0
        in x["0"] end"#
        ));
    }

    #[test]
    fn type_func() {
        assert!(type_ok(
            r#"
        let
            function odd(x: int): int =
                if x = 0 then 0 else even(x - 1)
            function even(x: int): int =
                if x = 0 then 1 else odd(x - 1)
        in odd(5) end"#
        ));
        assert!(type_fail(
            r#"
        let
            function f(x: int, y: string): string = y
        in f(1, 2) end"#
        ));
        assert!(type_fail(
            r#"
        let
            function f(x: int): int = x + 1
        in f(1, 2) end"#
        ));
        assert!(type_fail(
            r#"
        let
            function f(x: int): int = x + 1
        in f("z") end"#
        ));
    }

    #[test]
    fn type_expr() {
        assert!(type_ok(r#"let var x: int := {"a"; 0} in x end"#));
        assert!(type_fail(r#"let var x: int := {0; "a"} in x end"#));

        assert!(type_fail(r#"let in if "a" then 1 else 0 end"#));
        assert!(type_fail(r#"let in if 1 then "a" else 0 end"#));
        assert!(type_ok(r#"let in if 1 then "a" end"#));

        assert!(type_ok(
            r#"
        let
            var x: int := 5
        in
            for i := 0 to x do i + 1
        end"#
        ));
        assert!(type_fail(
            r#"
        let
            var x: string := "a"
        in
            for i := 0 to x do i + 1
        end"#
        ));
        assert!(type_ok(r#"let in while 1 do {} end"#));
        assert!(type_fail(r#"let in while "" do {} end"#));
    }
}
