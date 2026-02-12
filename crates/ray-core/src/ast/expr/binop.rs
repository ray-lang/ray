use serde::{Deserialize, Serialize};

use crate::ast::{Expr, InfixOp, Node};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinOp {
    pub lhs: Box<Node<Expr>>,
    pub rhs: Box<Node<Expr>>,
    pub op: Node<InfixOp>,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(binop {} {} {})", self.lhs, self.op, self.rhs)
    }
}
