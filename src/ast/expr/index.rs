use crate::{
    ast::{Expr, Node},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Index<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Box<Node<Expr<Info>, Info>>,
    pub index: Box<Node<Expr<Info>, Info>>,
    pub bracket_span: Span,
}

impl<Info> std::fmt::Display for Index<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(index {} {})",
            self.lhs.to_string(),
            self.index.to_string()
        )
    }
}
