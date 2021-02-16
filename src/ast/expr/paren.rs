use crate::ast::{Expr, Node};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Paren(pub Box<Node<Expr>>);

impl std::fmt::Display for Paren {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.0)
    }
}
