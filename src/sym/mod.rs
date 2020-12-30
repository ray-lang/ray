use crate::ast;

#[derive(Debug)]
pub struct Symbol {
    name: String,
    ty: ast::Type,
}
