use crate::ast::{Expr, Node};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Paren<Info>(pub Box<Node<Expr<Info>, Info>>)
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq;

impl<Info> std::fmt::Display for Paren<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.0)
    }
}
