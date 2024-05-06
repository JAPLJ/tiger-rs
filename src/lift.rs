// Lambda lifting

use std::collections::HashSet;

use rpds::HashTrieMap;

use crate::{
    absyn::Symbol,
    symtable::SymTable,
    typing::{Decl, EnvEntry, Expr, Func, VEnv, Var},
};

// function -> free variables (additional arguments)
type FEnv = HashTrieMap<Symbol, Vec<Symbol>>;

// free variable -> additional argument name
type REnv = HashTrieMap<Symbol, Symbol>;

pub fn lambda_lift(symt: &mut SymTable, e: &Expr) -> Expr {
    let venv = VEnv::new();
    let fenv = FEnv::new();
    let renv = REnv::new();
    let mut ll = LambdaLift::from_symt(symt);
    let e = ll.lift_exp(&venv, &renv, &fenv, e);
    Expr::Let(vec![Decl::Func(ll.top_fn)], Box::new(e))
}

struct LambdaLift<'a> {
    top_fn: Vec<Func>,
    symt: &'a mut SymTable,
}

impl<'a> LambdaLift<'a> {
    fn from_symt(symt: &'a mut SymTable) -> Self {
        LambdaLift {
            top_fn: vec![],
            symt,
        }
    }

    fn lift_exp(&mut self, venv: &VEnv, renv: &REnv, fenv: &FEnv, e: &Expr) -> Expr {
        match e {
            Expr::Var(v) => Expr::Var(Box::new(self.lift_var(venv, renv, fenv, v))),
            Expr::Nil => Expr::Nil,
            Expr::Int(x) => Expr::Int(*x),
            Expr::Str(s) => Expr::Str(s.to_string()),
            Expr::Call(f, args) => {
                let mut nargs = vec![];
                for fv in fenv.get(f).unwrap() {
                    nargs.push(Expr::Var(Box::new(Var::Simple(
                        *renv.get(fv).unwrap_or(fv),
                    ))));
                }
                for arg in args {
                    nargs.push(self.lift_exp(venv, renv, fenv, arg));
                }
                Expr::Call(*f, nargs)
            }
            Expr::BinOp(lhs, op, rhs) => Expr::BinOp(
                Box::new(self.lift_exp(venv, renv, fenv, lhs)),
                *op,
                Box::new(self.lift_exp(venv, renv, fenv, rhs)),
            ),
            Expr::Seq(es) => Expr::Seq(
                es.iter()
                    .map(|e| self.lift_exp(venv, renv, fenv, e))
                    .collect(),
            ),
            Expr::Assign(v, e) => Expr::Assign(
                Box::new(self.lift_var(venv, renv, fenv, v)),
                Box::new(self.lift_exp(venv, renv, fenv, e)),
            ),
            Expr::If(cond, th, el) => Expr::If(
                Box::new(self.lift_exp(venv, renv, fenv, cond)),
                Box::new(self.lift_exp(venv, renv, fenv, th)),
                el.as_ref()
                    .map(|e| Box::new(self.lift_exp(venv, renv, fenv, e))),
            ),
            Expr::While(cond, body) => Expr::While(
                Box::new(self.lift_exp(venv, renv, fenv, cond)),
                Box::new(self.lift_exp(venv, renv, fenv, body)),
            ),
            Expr::Break => Expr::Break,
            Expr::Let(decls, e) => {
                let mut tdecls = vec![];
                let (venv2, env2) =
                    decls
                        .iter()
                        .fold((venv.clone(), fenv.clone()), |(venv, env), decl| {
                            let (td, venv, env) = self.lift_dec(&venv, renv, &env, decl);
                            match td {
                                Decl::Func(fs) => self.top_fn.extend(fs),
                                Decl::Var(..) => tdecls.push(td),
                                Decl::Type(_) => {}
                            }
                            (venv, env)
                        });
                if tdecls.is_empty() {
                    self.lift_exp(&venv2, renv, &env2, e)
                } else {
                    Expr::Let(tdecls, Box::new(self.lift_exp(&venv2, renv, &env2, e)))
                }
            }
            Expr::Array(aty, size, init) => Expr::Array(
                aty.clone(),
                Box::new(self.lift_exp(venv, renv, fenv, size)),
                Box::new(self.lift_exp(venv, renv, fenv, init)),
            ),
        }
    }

    fn lift_var(&mut self, venv: &VEnv, renv: &REnv, fenv: &FEnv, v: &Var) -> Var {
        match v {
            Var::Simple(x) => Var::Simple(*renv.get(x).unwrap_or(x)),
            Var::Subscript(arr, ix) => Var::Subscript(
                Box::new(self.lift_var(venv, renv, fenv, arr)),
                self.lift_exp(venv, renv, fenv, ix),
            ),
        }
    }

    fn lift_dec(&mut self, venv: &VEnv, renv: &REnv, fenv: &FEnv, d: &Decl) -> (Decl, VEnv, FEnv) {
        match d {
            Decl::Var(nm, ty, e) => (
                Decl::Var(*nm, ty.clone(), self.lift_exp(venv, renv, fenv, e)),
                venv.insert(*nm, EnvEntry::Var(ty.clone())),
                fenv.clone(),
            ),
            Decl::Func(fs) => {
                let mut tfs = vec![];
                let mut fenv2 = fenv.clone();
                let mut fs_new_args = vec![];
                for f in fs {
                    let mut fv = self.free_exp(&f.body);
                    for (a, _, _) in &f.args {
                        fv.remove(a);
                    }

                    let mut fv_names = vec![];
                    let mut new_args = vec![];
                    let mut renv2 = renv.clone();
                    for v in fv {
                        if let Some(EnvEntry::Var(ty)) = venv.get(&v) {
                            let nv = self.symt.new_sym();
                            // call-by-reference for lifted args
                            new_args.push((nv, ty.clone(), true));
                            renv2.insert_mut(v, nv);
                            fv_names.push(v);
                        } else {
                            panic!(
                                "unexpected error: undefined variable {}, processing function {}",
                                self.symt.resolve(&v),
                                self.symt.resolve(&f.id),
                            );
                        }
                    }
                    fenv2.insert_mut(f.id, fv_names);
                    new_args.extend(f.args.clone());
                    fs_new_args.push((renv2, new_args));
                }

                for (f, (renv2, nargs)) in fs.iter().zip(fs_new_args) {
                    let venv2 = f.args.iter().fold(venv.clone(), |venv, (a, ty, _)| {
                        venv.insert(*a, EnvEntry::Var(ty.clone()))
                    });
                    tfs.push(Func {
                        id: f.id,
                        args: nargs,
                        result: f.result.clone(),
                        body: self.lift_exp(&venv2, &renv2, &fenv2, &f.body),
                    })
                }
                (Decl::Func(tfs), venv.clone(), fenv2)
            }
            Decl::Type(_) => (d.clone(), venv.clone(), fenv.clone()),
        }
    }

    fn union_fv(fvs: impl IntoIterator<Item = HashSet<Symbol>>) -> HashSet<Symbol> {
        let mut fv = HashSet::new();
        for s in fvs {
            fv.extend(s);
        }
        fv
    }

    fn free_exp(&mut self, e: &Expr) -> HashSet<Symbol> {
        match e {
            Expr::Var(v) => self.free_var(v),
            Expr::Nil | Expr::Int(_) | Expr::Str(_) => HashSet::new(),
            Expr::Call(_, args) => LambdaLift::union_fv(args.iter().map(|a| self.free_exp(a))),
            Expr::BinOp(lhs, _, rhs) => {
                LambdaLift::union_fv([self.free_exp(lhs), self.free_exp(rhs)])
            }
            Expr::Seq(es) => LambdaLift::union_fv(es.iter().map(|e| self.free_exp(e))),
            Expr::Assign(v, e) => LambdaLift::union_fv([self.free_var(v), self.free_exp(e)]),
            Expr::If(cond, th, el) => {
                let mut fv = LambdaLift::union_fv([self.free_exp(cond), self.free_exp(th)]);
                if let Some(el) = el {
                    fv.extend(self.free_exp(el));
                }
                fv
            }
            Expr::While(cond, body) => {
                LambdaLift::union_fv([self.free_exp(cond), self.free_exp(body)])
            }
            Expr::Break => HashSet::new(),
            Expr::Let(decls, e) => {
                let mut fv = self.free_exp(e);
                let mut decled = vec![];
                for d in decls {
                    let (fv2, nv) = self.free_dec(d);
                    fv.extend(fv2);
                    if let Some(v) = nv {
                        decled.push(v);
                    }
                }
                for v in decled {
                    fv.remove(&v);
                }
                fv
            }
            Expr::Array(_, size, init) => {
                LambdaLift::union_fv([self.free_exp(size), self.free_exp(init)])
            }
        }
    }

    fn free_var(&mut self, v: &Var) -> HashSet<Symbol> {
        match v {
            Var::Simple(x) => HashSet::from([*x]),
            Var::Subscript(arr, ix) => {
                LambdaLift::union_fv([self.free_var(arr), self.free_exp(ix)])
            }
        }
    }

    fn free_dec(&mut self, d: &Decl) -> (HashSet<Symbol>, Option<Symbol>) {
        match d {
            Decl::Var(nm, _, e) => (self.free_exp(e), Some(*nm)),
            Decl::Func(fs) => {
                let mut fvs = vec![];
                for f in fs {
                    let mut fv = self.free_exp(&f.body);
                    for (a, _, _) in &f.args {
                        fv.remove(a);
                    }
                    fvs.push(fv);
                }
                (LambdaLift::union_fv(fvs), None)
            }
            Decl::Type(_) => (HashSet::new(), None),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        alpha::alpha,
        lift::lambda_lift,
        parse,
        semant::{trans, Renamer},
        symtable::SymTable,
        test_util::tokenize_ok,
        typing::{Expr, TEnv, Type, VEnv},
    };
    use chumsky::prelude::*;

    fn lift(prog: &str) -> (Expr, SymTable) {
        let toks = tokenize_ok(prog);
        let (expr, symt, errs) = parse!(toks);
        assert!(errs.is_empty(), "parse error: {:?}", errs);
        let mut symt = SymTable::from_rodeo(symt.unwrap());

        let venv = VEnv::new();
        let tenv = TEnv::new()
            .insert(symt.get_or_intern("int"), Type::Int)
            .insert(symt.get_or_intern("string"), Type::String);

        let ((exp, _), errs) = trans(&mut symt, Renamer::new(), &venv, &tenv, &expr.unwrap());
        assert!(errs.is_empty(), "typecheck error: {:?}", errs);
        let exp = alpha(&mut symt, VEnv::new(), &exp);
        let exp = lambda_lift(&mut symt, &exp);
        (exp, symt)
    }

    #[test]
    fn check_lift() {
        let (e, symt) = lift(
            r#"
        let
            var a: int := 0
            function f(x: int, y: int): int =
                let
                    function g(z: int): int = a + x + z
                in
                    x + g(y)
                end
        in
            f(1, 2)
        end
        "#,
        );
        println!("{}", e.display(&symt))
    }
}
