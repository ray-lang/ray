//! Parse query infrastructure for the incremental compiler.

use ray_core::{
    ast::File,
    errors::RayError,
    parse::{ParseOptions, Parser},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{def::DefHeader, file_id::FileId};

use crate::{
    queries::workspace::{FileSource, WorkspaceSnapshot},
    query::{Database, Query},
};

/// Result of parsing a single source file.
#[derive(Clone)]
pub struct ParseResult {
    pub ast: File,
    pub defs: Vec<DefHeader>,
    pub source_map: SourceMap,
    pub errors: Vec<RayError>,
}

#[query]
pub fn parse_file(db: &Database, file_id: FileId) -> ParseResult {
    let source = db.get_input::<FileSource>(file_id);
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let file_info = workspace.file_info(file_id).expect("file not in workspace");

    let options = ParseOptions {
        module_path: file_info.module_path.to_path(),
        filepath: file_info.path.clone(),
        original_filepath: file_info.path.clone(),
        use_stdin: false,
    };

    let (ast, defs, source_map, errors) = Parser::parse_to_result(file_id, &source.0, options);

    ParseResult {
        ast: ast.unwrap_or_else(|| File {
            path: file_info.module_path.to_path(),
            stmts: vec![],
            decls: vec![],
            imports: vec![],
            doc_comment: None,
            filepath: file_info.path.clone(),
            span: ray_shared::span::Span::default(),
        }),
        defs,
        source_map,
        errors,
    }
}

#[cfg(test)]
mod tests {
    use ray_shared::pathlib::FilePath;

    use crate::{
        queries::{
            parse::parse_file,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    #[test]
    fn parse_query_returns_result() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let result = parse_file(&db, file_id);

        assert!(result.errors.is_empty());
        assert_eq!(result.defs.len(), 1);
        assert_eq!(result.defs[0].name, "main");
    }

    #[test]
    fn parse_query_deterministic_def_ids() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn foo() {}\nfn bar() {}".to_string());

        let result1 = parse_file(&db, file_id);
        let result2 = parse_file(&db, file_id);

        // Same source should produce same DefIds
        assert_eq!(result1.defs.len(), result2.defs.len());
        for (d1, d2) in result1.defs.iter().zip(result2.defs.iter()) {
            assert_eq!(d1.def_id, d2.def_id);
        }
    }

    #[test]
    fn parse_query_reports_errors() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main( {".to_string());

        let result = parse_file(&db, file_id);

        assert!(!result.errors.is_empty());
    }
}
