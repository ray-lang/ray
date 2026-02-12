use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Name, Node, token::Token};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Dot {
    pub lhs: Box<Node<Expr>>,
    pub rhs: Node<Name>,
    pub dot: Token,
}

impl std::fmt::Display for Dot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.lhs, self.rhs)
    }
}
