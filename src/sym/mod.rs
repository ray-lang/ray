use crate::ast;

#[derive(Clone, Debug)]
pub struct Symbol {
    name: String,
    ty: ast::Type,
}
