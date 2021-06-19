use crate::{
    ast::{Expr, Node, Sequence},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    pub lhs: Box<Node<Expr>>,
    pub args: Sequence,
    pub args_span: Span,
    pub paren_span: Span,
}

impl std::fmt::Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.items.len() == 0 {
            write!(f, "(call {})", self.lhs)
        } else {
            write!(f, "(call {} {})", self.lhs, self.args)
        }
    }
}

impl Call {
    pub fn new(lhs: Node<Expr>, args: Vec<Node<Expr>>) -> Self {
        Self {
            lhs: Box::new(lhs),
            args: Sequence::new(args),
            args_span: Span::new(),
            paren_span: Span::new(),
        }
    }
}
