use crate::ast::expr::Expr;
use crate::ast::pattern::Pattern;
use crate::ast::ty::Type;

#[derive(Clone, Debug)]
pub struct Local {
    pub is_mut: bool,
    pub pattern: Box<Pattern>,
    pub ty: Option<Type>,
    pub init: Option<Box<Expr>>,
}
