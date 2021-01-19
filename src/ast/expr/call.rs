use crate::{
    ast::{Expr, Node, Sequence, Type},
    span::Span,
    utils::join,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Box<Node<Expr<Info>, Info>>,
    pub ty_args: Option<(Vec<Type>, Span)>,
    pub args: Sequence<Info>,
    pub args_span: Span,
    pub paren_span: Span,
}

impl<Info> std::fmt::Display for Call<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ty_args = self
            .ty_args
            .as_ref()
            .map(|(tys, _)| format!("[{}]", join(tys, ",")))
            .unwrap_or_default();
        if self.args.items.len() == 0 {
            write!(f, "(call {}{})", self.lhs, ty_args)
        } else {
            write!(f, "(call {}{} {})", self.lhs, ty_args, self.args)
        }
    }
}
