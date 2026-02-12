use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node, PrefixOp};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnaryOp {
    pub expr: Box<Node<Expr>>,
    pub op: Node<PrefixOp>,
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(unaryop {} {})",
            self.op.to_string(),
            self.expr.to_string()
        )
    }
}
