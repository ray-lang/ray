use crate::ast::{Expr, Node};
use ray_shared::span::Span;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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
