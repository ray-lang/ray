use crate::{
    ast::{Expr, Node},
    span::Span,
};

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
pub struct Range<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub start: Box<Node<Expr<Info>, Info>>,
    pub end: Box<Node<Expr<Info>, Info>>,
    pub limits: RangeLimits,
    pub op_span: Span,
}

impl<Info> std::fmt::Display for Range<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(range {} {} {})", self.start, self.limits, self.end)
    }
}
