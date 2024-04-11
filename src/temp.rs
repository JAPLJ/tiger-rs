// Temporary (Registers + Labels)

use std::cell::{Cell, RefCell};

use lasso::Rodeo;

use crate::absyn::Symbol;

#[derive(PartialEq, Clone, Copy)]
pub struct Reg(u64);

impl ToString for Reg {
    fn to_string(&self) -> String {
        self.0.to_string()
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct Label(Symbol);
pub struct Temp {
    next_reg: Cell<u64>,
    next_label: Cell<u64>,
    labels: RefCell<Rodeo>,
}

impl Temp {
    pub fn new() -> Self {
        Temp {
            next_reg: Cell::new(0),
            next_label: Cell::new(0),
            labels: RefCell::new(Rodeo::new()),
        }
    }

    pub fn new_reg(&self) -> Reg {
        let r = self.next_reg.get();
        self.next_reg.set(r + 1);
        Reg(r)
    }

    pub fn new_label(&self) -> Label {
        let li = self.next_reg.get();
        let l = format!("_L{}", li);
        self.next_label.set(li + 1);
        self.named_label(l)
    }

    pub fn named_label(&self, name: impl AsRef<str>) -> Label {
        Label(self.labels.borrow_mut().get_or_intern(name))
    }
}
