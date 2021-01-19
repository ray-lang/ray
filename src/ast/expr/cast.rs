use crate::{
    ast::{Expr, Node, Type},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cast<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Box<Node<Expr<Info>, Info>>,
    pub ty: Type,
    pub as_span: Span,
}

impl<Info> std::fmt::Display for Cast<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(cast {} as {})", self.lhs, self.ty)
    }
}
