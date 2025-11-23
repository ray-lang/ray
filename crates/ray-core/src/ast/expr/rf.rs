use crate::ast::{Expr, Node};
use ray_shared::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ref {
    pub expr: Box<Node<Expr>>,
    pub op_span: Span,
}

impl std::fmt::Display for Ref {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(ref {})", self.expr.to_string())
    }
}
