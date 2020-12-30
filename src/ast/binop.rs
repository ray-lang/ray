use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct BinOp {
    pub lhs: Box<ast::Expr>,
    pub rhs: Box<ast::Expr>,
    pub op: ast::InfixOp,
    pub op_span: Span,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(binop {} {} {})", self.lhs, self.op, self.rhs)
    }
}
