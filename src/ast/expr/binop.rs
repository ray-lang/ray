use crate::{
    ast::{Expr, InfixOp, Node},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinOp {
    pub lhs: Box<Node<Expr>>,
    pub rhs: Box<Node<Expr>>,
    pub op: InfixOp,
    pub op_span: Span,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(binop {} {} {})", self.lhs, self.op, self.rhs)
    }
}
