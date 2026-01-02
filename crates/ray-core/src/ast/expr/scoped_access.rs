use crate::ast::{Expr, Name, Node, token::Token};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopedAccess {
    pub lhs: Box<Node<Expr>>,
    pub rhs: Node<Name>,
    pub sep: Token,
}

impl std::fmt::Display for ScopedAccess {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::{}", self.lhs, self.rhs)
    }
}

