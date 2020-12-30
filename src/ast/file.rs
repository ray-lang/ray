use crate::ast::{Decl, Expr, Import, Path};
use crate::pathlib::FilePath;
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct File {
    pub path: Path,
    pub stmts: Vec<Expr>,
    pub decls: Vec<Decl>,
    pub imports: Vec<Import>,
    pub doc_comment: Option<String>,
    pub filepath: FilePath,
    pub span: Span,
    pub last_ast_id: u64,
}
