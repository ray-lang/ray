pub mod anf;
mod basic_op;
mod builder;
mod size;
mod types;

pub use builder::*;
pub use types::*;

use crate::ast::Node;

pub fn malloc<T: Into<Value>>(size: T) -> Node<Value> {
    Node::new(Value::Call(
        Node::new(Callable::Op(Op::Malloc)),
        vec![Node::new(size.into())],
    ))
}

pub fn memcopy<T: Into<Value>>(dst: usize, src: usize, size: T) -> Node<Value> {
    Node::new(Value::Call(
        Node::new(Callable::Op(Op::MemCopy)),
        vec![
            Node::new(Value::Local(dst)), // dst
            Node::new(Value::Data(src)),  // src
            Node::new(size.into()),       // size
        ],
    ))
}
