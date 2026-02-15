use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

/// Nil-coalescing expression `lhs else rhs`.
///
/// Evaluates `lhs` (which should be nilable), and if it is `nil`, evaluates
/// and returns `rhs`. Otherwise returns the unwrapped value of `lhs`.
/// The `rhs` may be a divergent expression (`return`, `break`, `continue`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NilCoalesce {
    pub lhs: Box<Node<Expr>>,
    pub rhs: Box<Node<Expr>>,
}

impl std::fmt::Display for NilCoalesce {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} else {})", self.lhs, self.rhs)
    }
}
