use crate::ast::{Expr, Node, Pattern};
use ray_shared::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct For {
    pub pat: Node<Pattern>,
    pub expr: Box<Node<Expr>>,
    pub body: Box<Node<Expr>>,
    pub for_span: Span,
    pub in_span: Span,
}

impl std::fmt::Display for For {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(for {} in {} {})", self.pat, self.expr, self.body)
    }
}
