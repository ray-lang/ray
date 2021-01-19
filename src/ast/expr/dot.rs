use crate::ast::{token::Token, Expr, Name, Node};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dot<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Box<Node<Expr<Info>, Info>>,
    pub rhs: Name,
    pub dot: Token,
}

impl<Info> std::fmt::Display for Dot<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.lhs, self.rhs)
    }
}
