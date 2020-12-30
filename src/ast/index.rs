use crate::ast::Expr;
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct Index {
    pub lhs: Box<Expr>,
    pub index: Box<Expr>,
    pub bracket_span: Span,
}

impl std::fmt::Display for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(index {} {})",
            self.lhs.to_string(),
            self.index.to_string()
        )
    }
}
