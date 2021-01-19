use crate::{
    ast::{Expr, Node},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loop<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub body: Box<Node<Expr<Info>, Info>>,
    pub loop_span: Span,
}

impl<Info> std::fmt::Display for Loop<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(loop {})", self.body)
    }
}
