use ray_shared::span::Span;
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum RangeLimits {
    Inclusive,
    Exclusive,
}

impl std::fmt::Display for RangeLimits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                RangeLimits::Inclusive => "..=",
                RangeLimits::Exclusive => "..<",
            }
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Range {
    pub start: Box<Node<Expr>>,
    pub end: Box<Node<Expr>>,
    pub limits: RangeLimits,
    pub op_span: Span,
}

impl std::fmt::Display for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(range {} {} {})", self.start, self.limits, self.end)
    }
}
