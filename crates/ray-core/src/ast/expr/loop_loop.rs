use crate::ast::{Expr, Node};
use ray_shared::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loop {
    pub body: Box<Node<Expr>>,
    pub loop_span: Span,
}

impl std::fmt::Display for Loop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(loop {})", self.body)
    }
}
