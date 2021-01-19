use crate::{
    ast::{Expr, InfixOp, Node},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinOp<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Box<Node<Expr<Info>, Info>>,
    pub rhs: Box<Node<Expr<Info>, Info>>,
    pub op: InfixOp,
    pub op_span: Span,
}

impl<Info> std::fmt::Display for BinOp<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(binop {} {} {})", self.lhs, self.op, self.rhs)
    }
}
