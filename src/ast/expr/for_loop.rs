use crate::{
    ast::{Expr, Node, Pattern},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct For<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub pat: Pattern<Info>,
    pub expr: Box<Node<Expr<Info>, Info>>,
    pub body: Box<Node<Expr<Info>, Info>>,
    pub for_span: Span,
    pub in_span: Span,
}

impl<Info> std::fmt::Display for For<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(for {} in {} {})", self.pat, self.expr, self.body)
    }
}
