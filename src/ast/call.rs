use crate::span::Span;
use crate::{
    ast::{Expr, Sequence, Type},
    utils::join,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Call {
    pub lhs: Box<Expr>,
    pub ty_args: Option<(Vec<Type>, Span)>,
    pub args: Sequence,
    pub args_span: Span,
    pub paren_span: Span,
}

impl std::fmt::Display for Call {
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
