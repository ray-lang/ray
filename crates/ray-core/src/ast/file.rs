use crate::{
    ast::{Decl, Expr, Import, Node, Path},
    pathlib::FilePath,
    span::Span,
};

pub struct File {
    pub path: Path,
    pub stmts: Vec<Node<Expr>>,
    pub decls: Vec<Node<Decl>>,
    pub imports: Vec<Import>,
    pub doc_comment: Option<String>,
    pub filepath: FilePath,
    pub span: Span,
}
