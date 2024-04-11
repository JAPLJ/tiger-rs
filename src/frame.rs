use crate::temp;

pub trait Frame {
    type Access;

    fn name(&self) -> temp::Label;
    fn args(&self) -> &Vec<bool>;
    fn alloc_local(&mut self, temp: &temp::Temp, escaped: bool) -> Self::Access;
}

pub trait Frames {
    type Access;
    type Frame: Frame<Access = Self::Access>;

    fn new_frame(&mut self, name: temp::Label, args: Vec<bool>) -> Self::Frame;
}

pub enum LLVMAccess {
    InFrame(temp::Reg), // ptr variable returned by 'alloca'
    InReg(temp::Reg),
}

pub struct LLVMFrame {
    name: temp::Label,
    args: Vec<bool>,
}

impl Frame for LLVMFrame {
    type Access = LLVMAccess;

    fn name(&self) -> temp::Label {
        self.name
    }

    fn args(&self) -> &Vec<bool> {
        &self.args
    }

    fn alloc_local(&mut self, temp: &temp::Temp, escaped: bool) -> Self::Access {
        if escaped {
            Self::Access::InFrame(temp.new_reg())
        } else {
            Self::Access::InReg(temp.new_reg())
        }
    }
}

pub struct LLVMFrames {}

impl Frames for LLVMFrames {
    type Frame = LLVMFrame;
    type Access = LLVMAccess;

    fn new_frame(&mut self, name: temp::Label, args: Vec<bool>) -> Self::Frame {
        LLVMFrame { name, args }
    }
}
