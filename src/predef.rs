// predefined types and fnuctions

use crate::{
    semant::Renamer,
    symtable::SymTable,
    typing::{EnvEntry, TEnv, Type, VEnv},
};

pub fn types(symt: &mut SymTable) -> TEnv {
    TEnv::new()
        .insert(symt.get_or_intern("int"), Type::Int)
        .insert(symt.get_or_intern("string"), Type::String)
}

pub fn functions(symt: &mut SymTable) -> VEnv {
    VEnv::new()
        .insert(
            symt.get_or_intern("print"),
            EnvEntry::Func(vec![Type::String], Type::Unit),
        )
        .insert(
            symt.get_or_intern("flush"),
            EnvEntry::Func(vec![], Type::Unit),
        )
        .insert(
            symt.get_or_intern("getchar2"),
            EnvEntry::Func(vec![], Type::String),
        )
        .insert(
            symt.get_or_intern("ord"),
            EnvEntry::Func(vec![Type::String], Type::Int),
        )
        .insert(
            symt.get_or_intern("chr"),
            EnvEntry::Func(vec![Type::Int], Type::String),
        )
        .insert(
            symt.get_or_intern("size"),
            EnvEntry::Func(vec![Type::String], Type::Int),
        )
        .insert(
            symt.get_or_intern("substring"),
            EnvEntry::Func(vec![Type::String, Type::Int, Type::Int], Type::String),
        )
        .insert(
            symt.get_or_intern("concat"),
            EnvEntry::Func(vec![Type::String, Type::String], Type::String),
        )
        .insert(
            symt.get_or_intern("not"),
            EnvEntry::Func(vec![Type::Int], Type::Int),
        )
        .insert(
            symt.get_or_intern("exit"),
            EnvEntry::Func(vec![Type::Int], Type::Unit),
        )
}

pub fn renamer(symt: &mut SymTable) -> Renamer {
    // to avoid conflict with libc
    Renamer::new().insert(
        symt.get_or_intern("getchar"),
        symt.get_or_intern("getchar2"),
    )
}
