use rpds::HashTrieMap;

use crate::absyn::Symbol;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    String,
    Array(Box<Type>),
    Unit,
    Name(Symbol, Option<Box<Type>>),
}

impl Type {
    pub fn resolve(&self) -> Result<Self, Symbol> {
        match self {
            Type::Int => Ok(Type::Int),
            Type::String => Ok(Type::String),
            Type::Array(ty) => Ok(Type::Array(Box::new(ty.resolve()?))),
            Type::Unit => Ok(Type::Unit),
            Type::Name(sym, ty) => {
                if let Some(ty) = ty {
                    Ok(ty.resolve()?)
                } else {
                    Err(*sym)
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
