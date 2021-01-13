use crate::ast::{Expr, Type};
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Name {
    pub name: String,
    pub ty: Option<Type>,
    pub span: Span,
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref t) = self.ty {
            write!(f, "{}: {}", self.name, t)
        } else {
            write!(f, "{}", self.name)
        }
    }
}
