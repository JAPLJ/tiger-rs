use rpds::HashTrieMap;

use crate::absyn::{BinOp, Symbol};

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
    pub args: Vec<(Symbol, Type)>,
    pub result: Type,
    pub body: Expr,
}
