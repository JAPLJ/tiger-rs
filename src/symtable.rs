// Symbol table (wrapper for lasso::Rodeo)
use lasso::Rodeo;

use crate::absyn::Symbol;

pub struct SymTable {
    table: Rodeo,
    next_id: u64,
}

impl SymTable {
    pub fn from_rodeo(symt: Rodeo) -> Self {
        SymTable {
            table: symt,
            next_id: 0,
        }
    }

    pub fn table(&self) -> &Rodeo {
        &self.table
    }

    pub fn get_or_intern<T: AsRef<str>>(&mut self, k: T) -> Symbol {
        self.table.get_or_intern(k)
    }

    pub fn resolve(&self, k: &Symbol) -> &str {
        self.table.resolve(k)
    }

    pub fn new_sym(&mut self) -> Symbol {
        let id = self.next_id;
        self.next_id += 1;
        self.table.get_or_intern(format!("_T{}", id))
    }
}
