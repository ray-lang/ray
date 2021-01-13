use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cast {
    pub lhs: Box<ast::Expr>,
    pub ty: ast::Type,
    pub as_span: Span,
}

impl std::fmt::Display for Cast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(cast {} as {})", self.lhs, self.ty)
    }
}
