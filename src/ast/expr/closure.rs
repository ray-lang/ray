use crate::{
    ast::{Expr, Node, Sequence},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Closure<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub args: Sequence<Info>,
    pub body: Box<Node<Expr<Info>, Info>>,
    pub arrow_span: Option<Span>,
    pub curly_spans: Option<(Span, Span)>,
}

impl<Info> std::fmt::Display for Closure<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(closure {} => {})", self.args, self.body)
    }
}
