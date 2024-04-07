use rpds::HashTrieMap;

use crate::absyn::Symbol;

pub enum Type {
    Int,
    String,
    Array(Box<Type>),
    Unit,
    Name(Symbol, Option<Box<Type>>),
}

pub enum EnvEntry {
    Var(Type),
    Func(Vec<Type>, Type),
}

pub type TEnv = HashTrieMap<Symbol, Type>;
pub type VEnv = HashTrieMap<Symbol, EnvEntry>;
