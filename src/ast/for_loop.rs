use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct For {
    pub pat: ast::Pattern,
    pub expr: Box<ast::Expr>,
    pub body: Box<ast::Expr>,
    pub for_span: Span,
    pub in_span: Span,
}

impl std::fmt::Display for For {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(for {} in {} {})", self.pat, self.expr, self.body)
    }
}
