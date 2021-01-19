use crate::{ast, span::Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decorator<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub path: ast::Path,
    pub args: ast::Sequence<Info>,
    pub paren_sp: Span,
}
