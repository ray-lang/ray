use crate::{
    ast::{Decl, Expr, Import, Node, Path},
    pathlib::FilePath,
    span::Span,
};

pub struct File<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub path: Path,
    pub stmts: Vec<Node<Expr<Info>, Info>>,
    pub decls: Vec<Node<Decl<Info>, Info>>,
    pub imports: Vec<Import>,
    pub doc_comment: Option<String>,
    pub filepath: FilePath,
    pub span: Span,
}
