use crate::{
    ast::{Expr, Node},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Index {
    pub lhs: Box<Node<Expr>>,
    pub index: Box<Node<Expr>>,
    pub bracket_span: Span,
}

impl std::fmt::Display for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(index {} {})",
            self.lhs.to_string(),
            self.index.to_string()
        )
    }
}
