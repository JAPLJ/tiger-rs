use inkwell::{context::Context, types::BasicTypeEnum, AddressSpace};
use itertools::Itertools;
use rpds::HashTrieMap;
use std::fmt;

use crate::{
    absyn::{BinOp, Symbol},
    symtable::SymTable,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    String,
    Array(Box<Type>),
    Unit,
    Name(Symbol, Option<Box<Type>>),
}

impl Type {
    pub fn resolve(&self, tenv: &TEnv) -> Result<Type, Symbol> {
        match self {
            Type::Int => Ok(Type::Int),
            Type::String => Ok(Type::String),
            Type::Array(t) => Ok(Type::Array(Box::new(t.resolve(tenv)?))),
            Type::Unit => Ok(Type::Unit),
            Type::Name(nm, t) => {
                if let Some(t) = t {
                    t.resolve(&tenv)
                } else {
                    tenv.get(nm).cloned().ok_or(*nm)
                }
            }
        }
    }

    pub fn as_llvm_type<'ctx>(&self, ctx: &'ctx Context) -> BasicTypeEnum<'ctx> {
        match self {
            Type::Int => BasicTypeEnum::IntType(ctx.i64_type()),
            Type::String => BasicTypeEnum::PointerType(ctx.ptr_type(AddressSpace::default())),
            Type::Array(_) => BasicTypeEnum::PointerType(ctx.ptr_type(AddressSpace::default())),
            Type::Unit => BasicTypeEnum::PointerType(ctx.ptr_type(AddressSpace::default())),
            Type::Name(..) => panic!("unexpected error: type resolved"),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::String => write!(f, "string"),
            Type::Array(t) => write!(f, "array of {}", t),
            Type::Unit => write!(f, "unit"),
            Type::Name(nm, _) => write!(f, "_type{:?}", nm),
        }
    }
}

#[derive(Debug)]
pub enum EnvEntry {
    Var(Type),
    Func(Vec<Type>, Type),
}

pub type TEnv = HashTrieMap<Symbol, Type>;
pub type VEnv = HashTrieMap<Symbol, EnvEntry>;

#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    Simple(Symbol),
    Subscript(Box<Self>, Expr),
}

// Typed Expr without Span
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(Box<Var>),
    Nil,
    Int(i64),
    Str(String),
    Call(Symbol, Vec<Self>),
    BinOp(Box<Self>, BinOp, Box<Self>),
    Seq(Vec<Self>),
    Assign(Box<Var>, Box<Self>),
    If(Box<Self>, Box<Self>, Option<Box<Self>>),
    While(Box<Self>, Box<Self>),
    Break,
    Let(Vec<Decl>, Box<Self>),
    Array(Type, Box<Self>, Box<Self>),
}

impl Expr {
    pub fn display<'a>(&'a self, symt: &'a SymTable) -> Display<'a> {
        Display { e: self, symt }
    }

    fn fmt_var(f: &mut fmt::Formatter<'_>, v: &Var, symt: &SymTable) -> fmt::Result {
        match v {
            Var::Simple(s) => write!(f, "{}", symt.resolve(s)),
            Var::Subscript(arr, ix) => {
                Expr::fmt_var(f, arr, symt)?;
                write!(f, "[{}]", ix.display(symt))
            }
        }
    }

    fn fmt_dec(f: &mut fmt::Formatter<'_>, d: &Decl, symt: &SymTable) -> fmt::Result {
        match d {
            Decl::Var(nm, ty, e) => {
                write!(f, "{}: {} := {}", symt.resolve(nm), ty, e.display(symt))
            }
            Decl::Func(fs) => {
                for func in fs {
                    write!(
                        f,
                        "function {}({}): {} = {}\n",
                        symt.resolve(&func.id),
                        func.args
                            .iter()
                            .map(|(a, aty, r)| format!(
                                "{}: {}{}",
                                symt.resolve(a),
                                if *r { "&" } else { "" },
                                aty
                            ))
                            .join(", "),
                        func.result,
                        func.body.display(symt)
                    )?;
                }
                Ok(())
            }
            Decl::Type(ts) => {
                for (tn, ty) in ts {
                    write!(f, "type {} = {}\n", symt.resolve(tn), ty)?
                }
                Ok(())
            }
        }
    }
}

pub struct Display<'a> {
    e: &'a Expr,
    symt: &'a SymTable,
}

impl<'a> fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.e {
            Expr::Var(v) => Expr::fmt_var(f, v, self.symt),
            Expr::Nil => write!(f, "nil"),
            Expr::Int(x) => write!(f, "{}", x),
            Expr::Str(s) => write!(f, "{}", s),
            Expr::Call(func, args) => {
                write!(f, "{}", self.symt.resolve(func))?;
                write!(f, "(")?;
                write!(
                    f,
                    "{}",
                    args.iter().map(|a| a.display(self.symt)).join(", ")
                )?;
                write!(f, ")")
            }
            Expr::BinOp(lhs, op, rhs) => {
                write!(
                    f,
                    "({} {} {})",
                    lhs.display(self.symt),
                    op,
                    rhs.display(self.symt)
                )
            }
            Expr::Seq(es) => {
                write!(f, "{{")?;
                write!(f, "{}", es.iter().map(|e| e.display(self.symt)).join("; "))?;
                write!(f, "}}")
            }
            Expr::Assign(v, e) => {
                Expr::fmt_var(f, v, self.symt)?;
                write!(f, " := {}", e.display(self.symt))
            }
            Expr::If(cond, th, el) => {
                if let Some(el) = el {
                    write!(
                        f,
                        "if {} then {} else {}",
                        cond.display(self.symt),
                        th.display(self.symt),
                        el.display(self.symt)
                    )
                } else {
                    write!(
                        f,
                        "if {} then {}",
                        cond.display(self.symt),
                        th.display(self.symt)
                    )
                }
            }
            Expr::While(cond, body) => {
                write!(
                    f,
                    "while {} do {}",
                    cond.display(self.symt),
                    body.display(self.symt)
                )
            }
            Expr::Break => write!(f, "break"),
            Expr::Let(decls, e) => {
                write!(f, "let\n")?;
                for dec in decls {
                    Expr::fmt_dec(f, dec, self.symt)?;
                    write!(f, "\n")?;
                }
                write!(f, "in\n{}", e.display(self.symt))
            }
            Expr::Array(t, size, init) => {
                write!(
                    f,
                    "{} [{}] of size {}",
                    t,
                    init.display(self.symt),
                    size.display(self.symt)
                )
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Func(Vec<Func>),
    Var(
        // name, type, init
        Symbol,
        Type,
        Expr,
    ),
    Type(Vec<(Symbol, Type)>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Func {
    pub id: Symbol,
    // name, type, ref
    pub args: Vec<(Symbol, Type, bool)>,
    pub result: Type,
    pub body: Expr,
}
