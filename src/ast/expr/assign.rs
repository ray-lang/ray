use crate::{
    ast::{Expr, HasExpr, InfixOp, Node},
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assign<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Box<Node<Expr<Info>, Info>>,
    pub rhs: Box<Node<Expr<Info>, Info>>,
    pub is_mut: bool,
    pub mut_span: Option<Span>,
    pub op: InfixOp,
    pub op_span: Span,
}

impl<Info> std::fmt::Display for Assign<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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

impl<Info> Assign<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn get_ty_span(&self) -> Option<Span> {
        if let Expr::Name(n) = &self.lhs.expr() {
            n.ty.as_ref().and_then(|t| t.span().copied())
        } else {
            None
        }
    }
}
