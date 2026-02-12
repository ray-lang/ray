//! Parse query infrastructure for the incremental compiler.

use std::sync::Arc;

use serde::{Deserialize, Serialize};

use ray_core::{
    ast::{Decorator, File},
    errors::RayError,
    parse::{ParseOptions, Parser},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    def::{DefHeader, DefId},
    file_id::FileId,
    pathlib::Path,
    span::Span,
};

use crate::{
    queries::workspace::{FileSource, WorkspaceSnapshot},
    query::{Database, Query},
};

/// Result of parsing a single source file.
#[derive(Clone, Serialize, Deserialize)]
pub struct ParseResult {
    pub ast: File,
    pub defs: Vec<DefHeader>,
    pub source_map: SourceMap,
    pub errors: Vec<RayError>,
}

#[query]
pub fn parse_file(db: &Database, file_id: FileId) -> Arc<ParseResult> {
    let source = db.get_input::<FileSource>(file_id);
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let file_info = workspace.file_info(file_id).expect("file not in workspace");

    let options = ParseOptions {
        module_path: file_info.module_path.to_path(),
        filepath: file_info.path.clone(),
        original_filepath: file_info.path.clone(),
        use_stdin: false,
    };

    let (ast, defs, source_map, errors) =
        Parser::parse_to_result(file_id, source.as_str(), options);

    Arc::new(ParseResult {
        ast: ast.unwrap_or_else(|| File {
            path: file_info.module_path.to_path(),
            stmts: vec![],
            decls: vec![],
            imports: vec![],
            doc_comment: None,
            filepath: file_info.path.clone(),
            span: Span::default(),
        }),
        defs,
        source_map,
        errors,
    })
}

/// Returns the decorators attached to a definition.
///
/// Decorators are extracted from the source map using the definition's root node.
#[query]
pub fn decorators(db: &Database, def_id: DefId) -> Vec<Decorator> {
    let parse_result = parse_file(db, def_id.file);
    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id);

    let Some(def_header) = def_header else {
        return Vec::new();
    };

    parse_result
        .source_map
        .decorators()
        .get(&def_header.root_node)
        .cloned()
        .unwrap_or_default()
}

/// Checks if a definition has a decorator with the given name.
///
/// The name is matched against the decorator's path. For simple decorators
/// like `@inline`, the name would be "inline".
pub fn has_decorator(db: &Database, def_id: DefId, name: &str) -> bool {
    let decorators = decorators(db, def_id);
    let target_path = Path::from(name);
    decorators.iter().any(|d| d.path.value == target_path)
}

/// Returns the doc comment for a definition, if present.
#[query]
pub fn doc_comment(db: &Database, def_id: DefId) -> Option<String> {
    let parse_result = parse_file(db, def_id.file);
    let def_header = parse_result.defs.iter().find(|h| h.def_id == def_id)?;

    parse_result
        .source_map
        .doc_by_id(def_header.root_node)
        .cloned()
}

#[cfg(test)]
mod tests {
    use ray_shared::pathlib::{FilePath, Path};

    use crate::{
        queries::{
            parse::{decorators, doc_comment, has_decorator, parse_file},
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    #[test]
    fn parse_query_returns_result() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
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
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
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
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main( {".to_string());

        let result = parse_file(&db, file_id);

        assert!(!result.errors.is_empty());
    }

    #[test]
    fn decorators_returns_decorators_for_definition() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "@inline\nfn double(x: int) -> int => x * 2".to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        // Skip FileMain (index 0), function is index 1
        let fn_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "double")
            .expect("expected double function");

        let decorators = decorators(&db, fn_def.def_id);

        assert_eq!(decorators.len(), 1);
        assert_eq!(decorators[0].path.value.to_string(), "inline");
    }

    #[test]
    fn decorators_returns_empty_when_no_decorators() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let parse_result = parse_file(&db, file_id);
        let fn_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "main")
            .expect("expected main function");

        let decorators = decorators(&db, fn_def.def_id);

        assert!(decorators.is_empty());
    }

    #[test]
    fn has_decorator_returns_true_when_decorator_present() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "@inline\nfn double(x: int) -> int => x * 2".to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let fn_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "double")
            .expect("expected double function");

        assert!(has_decorator(&db, fn_def.def_id, "inline"));
        assert!(!has_decorator(&db, fn_def.def_id, "intrinsic"));
    }

    #[test]
    fn has_decorator_returns_false_when_no_decorators() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let parse_result = parse_file(&db, file_id);
        let fn_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "main")
            .expect("expected main function");

        assert!(!has_decorator(&db, fn_def.def_id, "inline"));
    }

    #[test]
    fn doc_comment_returns_comment_for_definition() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "/// This is a documented function.\nfn documented() {}".to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let fn_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "documented")
            .expect("expected documented function");

        let doc = doc_comment(&db, fn_def.def_id);

        assert!(doc.is_some());
        assert!(doc.unwrap().contains("This is a documented function"));
    }

    #[test]
    fn doc_comment_returns_none_when_no_doc() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn undocumented() {}".to_string());

        let parse_result = parse_file(&db, file_id);
        let fn_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "undocumented")
            .expect("expected undocumented function");

        let doc = doc_comment(&db, fn_def.def_id);

        assert!(doc.is_none());
    }

    #[test]
    fn parses_path_with_type_arguments() {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        let src = r#"
map = std::collections::HashMap[u32, string]::create()
"#;
        FileSource::new(&db, file_id, src.to_string());
        let parse_result = parse_file(&db, file_id);

        assert!(
            parse_result.errors.is_empty(),
            "expected no errors: {:?}",
            parse_result.errors
        );

        eprintln!("{:?}", parse_result.ast.decls);
    }
}
