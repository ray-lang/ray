use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct Loop {
    pub body: Box<ast::Expr>,
    pub loop_span: Span,
}

impl std::fmt::Display for Loop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(loop {})", self.body)
    }
}
