use crate::{
    ast::{Expr, Node},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct While {
    pub cond: Box<Node<Expr>>,
    pub body: Box<Node<Expr>>,
    pub while_span: Span,
}

impl std::fmt::Display for While {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(while {} {})",
            self.cond.to_string(),
            self.body.to_string()
        )
    }
}
