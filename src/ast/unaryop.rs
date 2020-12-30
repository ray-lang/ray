use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct UnaryOp {
    pub expr: Box<ast::Expr>,
    pub op: ast::PrefixOp,
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
