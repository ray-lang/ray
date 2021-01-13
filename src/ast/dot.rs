use crate::ast::token::Token;
use crate::ast::{Expr, Name};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dot {
    pub lhs: Box<Expr>,
    pub rhs: Name,
    pub dot: Token,
    pub desugared: Option<Box<Expr>>,
}

impl std::fmt::Display for Dot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.lhs, self.rhs)
    }
}
