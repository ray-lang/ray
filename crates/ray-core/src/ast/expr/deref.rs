use crate::{
    ast::{Expr, Node},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Deref {
    pub expr: Box<Node<Expr>>,
    pub op_span: Span,
}

impl std::fmt::Display for Deref {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(deref {})", self.expr.to_string())
    }
}
