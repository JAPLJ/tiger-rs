// Rename symbols (alpha-conversion)
use rpds::HashTrieMap;

use crate::{
    absyn::Symbol,
    symtable::SymTable,
    typing::{self, Decl, Expr, VEnv, Var},
};

type Env = HashTrieMap<Symbol, Symbol>;

pub fn alpha(symt: &mut SymTable, ext_fs: VEnv, e: &Expr) -> Expr {
    let env = Env::new();
    let mut a = Alpha::from_symt(symt, ext_fs);
    a.alpha_exp(&env, e)
}

struct Alpha<'a> {
    symt: &'a mut SymTable,
    ext_fs: VEnv,
}

impl<'a> Alpha<'a> {
    fn from_symt(symt: &'a mut SymTable, ext_fs: VEnv) -> Self {
        Alpha { symt, ext_fs }
    }

    fn find(env: &Env, s: &Symbol) -> Symbol {
        *env.get(s).unwrap()
    }

    fn alpha_exp(&mut self, env: &Env, e: &Expr) -> Expr {
        match e {
            Expr::Var(v) => Expr::Var(Box::new(self.alpha_var(env, v))),
            Expr::Nil => Expr::Nil,
            Expr::Int(x) => Expr::Int(*x),
            Expr::Str(s) => Expr::Str(s.to_string()),
            Expr::Call(f, args) => Expr::Call(
                if self.ext_fs.contains_key(f) {
                    *f
                } else {
                    Alpha::find(env, f)
                },
                args.iter().map(|e| self.alpha_exp(env, e)).collect(),
            ),
            Expr::BinOp(lhs, op, rhs) => Expr::BinOp(
                Box::new(self.alpha_exp(env, lhs)),
                *op,
                Box::new(self.alpha_exp(env, rhs)),
            ),
            Expr::Seq(es) => Expr::Seq(es.iter().map(|e| self.alpha_exp(env, e)).collect()),
            Expr::Assign(v, e) => Expr::Assign(
                Box::new(self.alpha_var(env, v)),
                Box::new(self.alpha_exp(env, e)),
            ),
            Expr::If(cond, th, el) => Expr::If(
                Box::new(self.alpha_exp(env, cond)),
                Box::new(self.alpha_exp(env, th)),
                el.as_ref().map(|e| Box::new(self.alpha_exp(env, e))),
            ),
            Expr::While(cond, body) => Expr::While(
                Box::new(self.alpha_exp(env, cond)),
                Box::new(self.alpha_exp(env, body)),
            ),
            Expr::Break => Expr::Break,
            Expr::Let(decls, e) => {
                let mut tdecls = vec![];
                let env2 = decls.iter().fold(env.clone(), |env, decl| {
                    let (td, env) = self.alpha_dec(&env, decl);
                    tdecls.push(td);
                    env
                });
                Expr::Let(tdecls, Box::new(self.alpha_exp(&env2, e)))
            }
            Expr::Array(aty, size, init) => Expr::Array(
                aty.clone(),
                Box::new(self.alpha_exp(env, size)),
                Box::new(self.alpha_exp(env, init)),
            ),
        }
    }

    fn alpha_var(&mut self, env: &Env, v: &Var) -> Var {
        match v {
            Var::Simple(x) => Var::Simple(Alpha::find(env, x)),
            Var::Subscript(arr, ix) => {
                Var::Subscript(Box::new(self.alpha_var(env, arr)), self.alpha_exp(env, ix))
            }
        }
    }

    fn alpha_dec(&mut self, env: &Env, d: &Decl) -> (Decl, Env) {
        match d {
            Decl::Var(nm, ty, e) => {
                let e = self.alpha_exp(env, e);
                let new_name = self.symt.new_sym();
                (
                    Decl::Var(new_name, ty.clone(), e),
                    env.insert(*nm, new_name),
                )
            }
            Decl::Func(fs) => {
                let env = fs
                    .iter()
                    .fold(env.clone(), |env, f| env.insert(f.id, self.symt.new_sym()));
                let mut tfs = vec![];
                for f in fs {
                    let mut targs = vec![];
                    let env2 = f.args.iter().fold(env.clone(), |env, (arg, argty, rf)| {
                        let new_argname = self.symt.new_sym();
                        targs.push((new_argname, argty.clone(), *rf));
                        env.insert(*arg, new_argname)
                    });
                    let body = self.alpha_exp(&env2, &f.body);
                    tfs.push(typing::Func {
                        id: Alpha::find(&env, &f.id),
                        args: targs,
                        result: f.result.clone(),
                        body,
                    })
                }
                (Decl::Func(tfs), env)
            }
            Decl::Type(_) => (d.clone(), env.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        alpha::alpha,
        parse,
        semant::{trans, Renamer},
        symtable::SymTable,
        test_util::tokenize_ok,
        typing::{Expr, TEnv, Type, VEnv},
    };
    use chumsky::prelude::*;

    fn alpha_conv(prog: &str) -> (Expr, SymTable) {
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
        (exp, symt)
    }

    #[test]
    fn check_alpha() {
        let (e, symt) = alpha_conv(
            r#"
        let
            var x := 0
            function f(a: int, b: int): int = x + a + (
                let
                    var x := x + a
                    function f(z: int): int = z + x
                in x + f(b) end
            )
        in f(1, 2) end
        "#,
        );
        println!("{}", e.display(&symt))
    }
}
