use crate::{
    ast::{Expr, Node, Sequence},
    span::Span,
    typing::ty::Ty,
    utils::join,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Box<Node<Expr<Info>, Info>>,
    pub args: Sequence<Info>,
    pub args_span: Span,
    pub paren_span: Span,
}

impl<Info> std::fmt::Display for Call<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.items.len() == 0 {
            write!(f, "(call {})", self.lhs)
        } else {
            write!(f, "(call {} {})", self.lhs, self.args)
        }
    }
}
