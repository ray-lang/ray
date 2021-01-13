use crate::ast;
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assign {
    pub lhs: Box<ast::Expr>,
    pub rhs: Box<ast::Expr>,
    pub is_mut: bool,
    pub mut_span: Option<Span>,
    pub op: ast::InfixOp,
    pub op_span: Span,
}

impl std::fmt::Display for Assign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(assign{} {} {} {})",
            if self.is_mut { " mut" } else { "" },
            self.lhs,
            self.op,
            self.rhs,
        )
    }
}

impl Assign {
    pub fn get_ty_span(&self) -> Option<Span> {
        if let ast::ExprKind::Name(n) = &self.lhs.kind {
            n.ty.as_ref().map(|t| t.span).unwrap_or_default()
        } else {
            None
        }
    }
}
