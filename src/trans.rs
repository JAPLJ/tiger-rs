// Type Checker + Translator
use lasso::Rodeo;

use crate::{
    absyn::{self, Spanned},
    lex::Span,
    types::{self, TEnv, VEnv},
};

pub type ExpTy = ((), types::Type);

pub type Error = (String, String, Span);

macro_rules! check_type {
    ($t:expr, $exp_t:expr, $span:expr, $errs:ident) => {{
        if $t != $exp_t {
            $errs.push((
                format!("mismatched types"),
                format!("expected {:?}, found {:?}", $exp_t, $t),
                $span,
            ));
        }
    }};
}

pub fn trans_exp(
    symt: &Rodeo,
    venv: &VEnv,
    tenv: &TEnv,
    e: &Spanned<absyn::Expr>,
) -> (ExpTy, Vec<Error>) {
    let mut errs = vec![];
    (inner(symt, venv, tenv, e, &mut errs), errs)
}

fn inner(
    symt: &Rodeo,
    venv: &VEnv,
    tenv: &TEnv,
    e: &Spanned<absyn::Expr>,
    errs: &mut Vec<Error>,
) -> ExpTy {
    let (e, span) = e;
    match e {
        absyn::Expr::Var(v) => trans_var(symt, venv, tenv, &(v.as_ref().clone(), *span), errs),
        absyn::Expr::Nil => unimplemented!(),
        absyn::Expr::Int(_) => ((), types::Type::Int),
        absyn::Expr::Str(_) => ((), types::Type::String),
        absyn::Expr::Call(f, args) => {
            if let Some(ft) = venv.get(&f) {
                if let types::EnvEntry::Func(aty, rty) = ft {
                    if args.len() != aty.len() {
                        errs.push((
                            format!("unexpected number of arguments"),
                            format!("expected {} arguments, found {}", aty.len(), args.len()),
                            *span,
                        ));
                        ((), rty.clone())
                    } else {
                        let _args = args
                            .iter()
                            .zip(aty)
                            .map(|(a, ty)| {
                                let (_, t) = inner(symt, venv, tenv, a, errs);
                                check_type!(t, *ty, a.1, errs);
                                ((), t)
                            })
                            .collect::<Vec<_>>();
                        ((), rty.clone())
                    }
                } else {
                    errs.push((
                        format!("call expression requires function"),
                        format!("{} has type {:?}", symt.resolve(&f), ft),
                        *span,
                    ));
                    ((), types::Type::Int)
                }
            } else {
                errs.push((
                    format!("cannot find function"),
                    format!("{} is not defined here", symt.resolve(&f)),
                    *span,
                ));
                ((), types::Type::Int)
            }
        }
        absyn::Expr::BinOp(lhs, _op, rhs) => {
            let (_, lt) = inner(symt, venv, tenv, lhs.as_ref(), errs);
            let (_, rt) = inner(symt, venv, tenv, rhs.as_ref(), errs);
            check_type!(lt, types::Type::Int, (*lhs).1, errs);
            check_type!(rt, types::Type::Int, (*rhs).1, errs);
            ((), types::Type::Int)
        }
        absyn::Expr::Seq(es) => es
            .iter()
            .map(|e| inner(symt, venv, tenv, e, errs))
            .last()
            .unwrap_or(((), types::Type::Unit)),
        absyn::Expr::Assign(v, e) => {
            let (_, vt) = trans_var(symt, venv, tenv, &v, errs);
            let (_, et) = inner(symt, venv, tenv, &e, errs);
            check_type!(et, vt, (*e).1, errs);
            ((), types::Type::Unit)
        }
        absyn::Expr::If(cond, th, el) => {
            let (_, ct) = inner(symt, venv, tenv, &cond, errs);
            check_type!(ct, types::Type::Int, (*cond).1, errs);
            let (_, tt) = inner(symt, venv, tenv, &th, errs);
            if let Some(el) = el {
                let (_, et) = inner(symt, venv, tenv, &el, errs);
                check_type!(tt, et, (*el).1, errs);
                ((), tt)
            } else {
                ((), types::Type::Unit)
            }
        }
        absyn::Expr::While(cond, e) => {
            let (_, ct) = inner(symt, venv, tenv, &cond, errs);
            check_type!(ct, types::Type::Int, (*cond).1, errs);
            let _ = inner(symt, venv, tenv, &e, errs);
            ((), types::Type::Unit)
        }
        absyn::Expr::For(v, from, to, e) => {
            let (_, ft) = inner(symt, venv, tenv, &from, errs);
            let (_, tt) = inner(symt, venv, tenv, &to, errs);
            check_type!(ft, types::Type::Int, (*from).1, errs);
            check_type!(tt, types::Type::Int, (*to).1, errs);
            let venv2 = venv.insert(*v, types::EnvEntry::Var(types::Type::Int));
            let _ = inner(symt, &venv2, tenv, &e, errs);
            ((), types::Type::Unit)
        }
        absyn::Expr::Break => {
            // TODO: check if inside a loop
            ((), types::Type::Unit)
        }
        absyn::Expr::Let(decls, e) => {
            let (venv2, tenv2) = decls
                .iter()
                .fold((venv.clone(), tenv.clone()), |(ve, te), decl| {
                    trans_dec(&ve, &te, decl, errs)
                });
            let (_, t) = inner(symt, &venv2, &tenv2, &e, errs);
            ((), t)
        }
        absyn::Expr::Array(atys, size, init) => {
            if let Some(aty) = tenv.get(&atys) {
                if let types::Type::Array(ety) = aty {
                    let (_, st) = inner(symt, venv, tenv, &size, errs);
                    check_type!(st, types::Type::Int, (*size).1, errs);
                    let (_, it) = inner(symt, venv, tenv, &init, errs);
                    check_type!(it, **ety, (*init).1, errs);
                    ((), aty.clone())
                } else {
                    errs.push((
                        format!("cannot create array"),
                        format!("{} has type {:?}, not array", symt.resolve(atys), aty),
                        *span,
                    ));
                    ((), types::Type::Int)
                }
            } else {
                errs.push((
                    format!("cannot find type"),
                    format!("{} is not defined here", symt.resolve(atys)),
                    *span,
                ));
                ((), types::Type::Int)
            }
        }
    }
}

fn trans_var(
    symt: &Rodeo,
    venv: &VEnv,
    tenv: &TEnv,
    v: &Spanned<absyn::Var>,
    errs: &mut Vec<Error>,
) -> ExpTy {
    let (v, span) = v;
    match v {
        absyn::Var::Simple(sym) => {
            if let Some(entry) = venv.get(sym) {
                if let types::EnvEntry::Var(ty) = entry {
                    let ty = ty.resolve().unwrap_or_else(|sym| {
                        errs.push((
                            format!("cannot find type"),
                            format!("{} is not defined here", symt.resolve(&sym)),
                            *span,
                        ));
                        types::Type::Int
                    });
                    ((), ty)
                } else {
                    errs.push((
                        format!("function is not a variable"),
                        format!("{} is function, not variable", symt.resolve(sym)),
                        *span,
                    ));
                    ((), types::Type::Int)
                }
            } else {
                errs.push((
                    format!("cannot find variable"),
                    format!("{} is not defined here", symt.resolve(sym)),
                    *span,
                ));
                ((), types::Type::Int)
            }
        }
        absyn::Var::Subscript(arr, ix) => {
            let (_, aty) = trans_var(symt, venv, tenv, arr, errs);
            if let types::Type::Array(ety) = aty {
                let (_, ity) = inner(symt, venv, tenv, ix, errs);
                check_type!(ity, types::Type::Int, ix.1, errs);
                ((), *ety)
            } else {
                errs.push((
                    format!("subscript requires array"),
                    format!("this has type {:?}", aty),
                    *span,
                ));
                ((), types::Type::Int)
            }
        }
    }
}

fn trans_dec(venv: &VEnv, tenv: &TEnv, d: &absyn::Decl, errs: &mut Vec<Error>) -> (VEnv, TEnv) {
    todo!()
}

fn trans_ty(tenv: &TEnv, t: &absyn::Type) -> types::Type {
    todo!()
}
