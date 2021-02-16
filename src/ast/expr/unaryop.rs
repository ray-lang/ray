use crate::{
    ast::{Expr, Node, PrefixOp},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnaryOp {
    pub expr: Box<Node<Expr>>,
    pub op: PrefixOp,
    pub op_span: Span,
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(unaryop {} {})",
            self.op.to_string(),
            self.expr.to_string()
        )
    }
}
