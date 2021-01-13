use crate::ast::{self, Sequence};
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decorator {
    pub path: ast::Path,
    pub args: Sequence,
    pub paren_sp: Span,
}
