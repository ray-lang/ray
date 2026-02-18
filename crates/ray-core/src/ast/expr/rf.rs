use ray_shared::span::Span;
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Ref {
    pub expr: Box<Node<Expr>>,
    pub mutable: bool,
    pub op_span: Span,
}

impl std::fmt::Display for Ref {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.mutable {
            write!(f, "(ref mut {})", self.expr)
        } else {
            write!(f, "(ref {})", self.expr)
        }
    }
}
