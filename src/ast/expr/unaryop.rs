use crate::{
    ast::{Expr, Node, PrefixOp},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnaryOp<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub expr: Box<Node<Expr<Info>, Info>>,
    pub op: PrefixOp,
    pub op_span: Span,
}

impl<Info> std::fmt::Display for UnaryOp<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(unaryop {} {})",
            self.op.to_string(),
            self.expr.to_string()
        )
    }
}
