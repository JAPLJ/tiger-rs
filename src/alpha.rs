// Rename symbols (alpha-conversion)
use rpds::HashTrieMap;

use crate::{
    absyn::Symbol,
    symtable::SymTable,
    typing::{self, Decl, Expr, Var},
};

type Env = HashTrieMap<Symbol, Symbol>;

fn find(env: &Env, s: &Symbol) -> Symbol {
    *env.get(s).unwrap()
}

pub fn alpha(symt: &mut SymTable, e: &Expr) -> Expr {
    let env = Env::new();
    inner(symt, &env, e)
}

fn inner(symt: &mut SymTable, env: &Env, e: &Expr) -> Expr {
    match e {
        Expr::Var(v) => Expr::Var(Box::new(alpha_var(symt, env, v))),
        Expr::Nil => Expr::Nil,
        Expr::Int(x) => Expr::Int(*x),
        Expr::Str(s) => Expr::Str(s.to_string()),
        Expr::Call(f, args) => Expr::Call(
            find(env, f),
            args.iter().map(|e| inner(symt, env, e)).collect(),
        ),
        Expr::BinOp(lhs, op, rhs) => Expr::BinOp(
            Box::new(inner(symt, env, lhs)),
            *op,
            Box::new(inner(symt, env, rhs)),
        ),
        Expr::Seq(es) => Expr::Seq(es.iter().map(|e| inner(symt, env, e)).collect()),
        Expr::Assign(v, e) => Expr::Assign(
            Box::new(alpha_var(symt, env, v)),
            Box::new(inner(symt, env, e)),
        ),
        Expr::If(cond, th, el) => Expr::If(
            Box::new(inner(symt, env, cond)),
            Box::new(inner(symt, env, th)),
            el.as_ref().map(|e| Box::new(inner(symt, env, e))),
        ),
        Expr::While(cond, body) => Expr::While(
            Box::new(inner(symt, env, cond)),
            Box::new(inner(symt, env, body)),
        ),
        Expr::Break => Expr::Break,
        Expr::Let(decls, e) => {
            let mut tdecls = vec![];
            let env2 = decls.iter().fold(env.clone(), |env, decl| {
                let (td, env) = alpha_dec(symt, &env, decl);
                tdecls.push(td);
                env
            });
            Expr::Let(tdecls, Box::new(inner(symt, &env2, e)))
        }
        Expr::Array(aty, size, init) => Expr::Array(
            aty.clone(),
            Box::new(inner(symt, env, size)),
            Box::new(inner(symt, env, init)),
        ),
    }
}

fn alpha_var(symt: &mut SymTable, env: &Env, v: &Var) -> Var {
    match v {
        Var::Simple(x) => Var::Simple(find(env, x)),
        Var::Subscript(arr, ix) => {
            Var::Subscript(Box::new(alpha_var(symt, env, arr)), inner(symt, env, ix))
        }
    }
}

fn alpha_dec(symt: &mut SymTable, env: &Env, d: &Decl) -> (Decl, Env) {
    match d {
        Decl::Var(nm, ty, e) => {
            let e = inner(symt, env, e);
            let new_name = symt.new_sym();
            (
                Decl::Var(new_name, ty.clone(), e),
                env.insert(*nm, new_name),
            )
        }
        Decl::Func(fs) => {
            let env = fs
                .iter()
                .fold(env.clone(), |env, f| env.insert(f.id, symt.new_sym()));
            let mut tfs = vec![];
            for f in fs {
                let mut targs = vec![];
                let env2 = f.args.iter().fold(env.clone(), |env, (arg, argty, rf)| {
                    let new_argname = symt.new_sym();
                    targs.push((new_argname, argty.clone(), *rf));
                    env.insert(*arg, new_argname)
                });
                let body = inner(symt, &env2, &f.body);
                tfs.push(typing::Func {
                    id: find(&env, &f.id),
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

#[cfg(test)]
mod tests {
    use crate::{
        alpha::alpha,
        parse,
        semant::trans,
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

        let ((exp, _), errs) = trans(&mut symt, &venv, &tenv, &expr.unwrap());
        assert!(errs.is_empty(), "typecheck error: {:?}", errs);
        let exp = alpha(&mut symt, &exp);
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
