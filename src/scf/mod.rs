pub enum ControlKind {
    Block,
    Loop,
    Break,
    Continue,
}

pub struct ControlBlock<T> {
    kind: ControlKind,
    values: Vec<T>,
}

pub trait ToControlBlock {
    fn to_control_block(&self) -> ControlBlock<Self>
    where
        Self: Sized;
}
