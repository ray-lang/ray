use ray_shared::span::Span;

use crate::ast::{Expr, Node};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Boxed {
    pub inner: Box<Node<Expr>>,
    pub box_span: Span,
}

impl std::fmt::Display for Boxed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(box {})", self.inner)
    }
}
