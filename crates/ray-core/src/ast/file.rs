use ray_shared::{
    pathlib::{FilePath, Path},
    span::Span,
};
use serde::{Deserialize, Serialize};

use crate::ast::{Decl, Expr, Import, Node};

#[derive(Clone, Serialize, Deserialize)]
pub struct File {
    pub path: Path,
    pub stmts: Vec<Node<Expr>>,
    pub decls: Vec<Node<Decl>>,
    pub imports: Vec<Import>,
    pub doc_comment: Option<String>,
    pub filepath: FilePath,
    pub span: Span,
}
