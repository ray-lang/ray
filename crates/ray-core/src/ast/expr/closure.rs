use crate::ast::{Expr, Node, Sequence};
use ray_shared::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Closure {
    pub args: Sequence,
    pub body: Box<Node<Expr>>,
    pub arrow_span: Option<Span>,
    pub curly_spans: Option<(Span, Span)>,
}

impl std::fmt::Display for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(closure {} => {})", self.args, self.body)
    }
}
