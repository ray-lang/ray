use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct Closure {
    pub args: ast::Sequence,
    pub body: Box<ast::Expr>,
    pub arrow_span: Option<Span>,
    pub curly_spans: Option<(Span, Span)>,
}

impl std::fmt::Display for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(closure {} => {})", self.args, self.body)
    }
}
