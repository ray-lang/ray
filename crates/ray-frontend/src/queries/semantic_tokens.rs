//! Semantic tokens query for LSP syntax highlighting.
//!
//! Produces a list of semantic tokens for a file by walking the transformed AST.
//! Each token carries a span, token kind, and optional modifiers. The LSP layer
//! is responsible for converting these span-based tokens into the delta-encoded
//! format required by the `textDocument/semanticTokens/full` protocol.

use std::sync::Arc;

use ray_core::ide::semantic_tokens::{self as core_semantic_tokens, SemanticToken};
use ray_query_macros::query;
use ray_shared::file_id::FileId;

use crate::{
    queries::parse::parse_file,
    query::{Database, Query},
};

/// Result of the `semantic_tokens` query.
///
/// Contains a sorted list of span-based semantic tokens suitable for
/// syntax highlighting. Tokens cover keywords, functions, variables,
/// types, comments, and other syntactic constructs.
#[derive(Clone)]
pub struct SemanticTokens {
    pub data: Vec<SemanticToken>,
}

/// Produces semantic tokens for a file.
///
/// Depends on `parse_file` to obtain the raw (untransformed) AST and source
/// map. Using the raw AST avoids walking synthetic nodes introduced by
/// `file_ast` transformations (desugaring, shorthand expansion, etc.) which
/// may lack proper source spans.
///
/// Parse errors do not prevent token generation for valid AST nodes.
///
/// TODO: Wire in `name_resolutions` for resolution-aware classification.
/// Currently classification is purely syntactic (based on AST position).
/// With resolutions we could distinguish e.g. a `Name` that refers to a
/// function vs. a type vs. a variable, and classify scoped access members
/// as `Method` when appropriate.
#[query]
pub fn semantic_tokens(db: &Database, file_id: FileId) -> Arc<SemanticTokens> {
    let parse_result = parse_file(db, file_id);
    let tokens = core_semantic_tokens::collect(&parse_result.ast, &parse_result.source_map);
    Arc::new(SemanticTokens { data: tokens })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_core::ide::semantic_tokens::{SemanticTokenKind, SemanticTokenModifier};
    use ray_shared::{
        file_id::FileId,
        pathlib::{FilePath, Path},
    };

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            semantic_tokens::semantic_tokens,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_db(source: &str) -> (Database, FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        FileSource::new(&db, file_id, source.to_string());
        (db, file_id)
    }

    #[test]
    fn semantic_tokens_returns_tokens_for_function() {
        let (db, file_id) = setup_db("fn foo() {}");
        let result = semantic_tokens(&db, file_id);

        assert!(!result.data.is_empty(), "should produce tokens");

        // Should contain a Function token for "foo"
        let has_function = result
            .data
            .iter()
            .any(|t| t.kind == SemanticTokenKind::Function);
        assert!(has_function, "should have a Function token");
    }

    #[test]
    fn semantic_tokens_classifies_keywords() {
        let (db, file_id) = setup_db("fn main() { x = 1 }");
        let result = semantic_tokens(&db, file_id);

        let has_keyword = result
            .data
            .iter()
            .any(|t| t.kind == SemanticTokenKind::Keyword);
        assert!(has_keyword, "should have Keyword tokens (fn)");
    }

    #[test]
    fn semantic_tokens_classifies_variables() {
        let (db, file_id) = setup_db("fn main() { x = 42 }");
        let result = semantic_tokens(&db, file_id);

        let has_variable = result
            .data
            .iter()
            .any(|t| t.kind == SemanticTokenKind::Variable);
        assert!(has_variable, "should have Variable tokens");
    }

    #[test]
    fn semantic_tokens_classifies_types() {
        let (db, file_id) = setup_db("struct Point { x: int, y: int }");
        let result = semantic_tokens(&db, file_id);

        let has_type = result
            .data
            .iter()
            .any(|t| t.kind == SemanticTokenKind::Type);
        assert!(has_type, "should have Type tokens");
    }

    #[test]
    fn semantic_tokens_classifies_string_literals() {
        let (db, file_id) = setup_db("fn main() { s = \"hello\" }");
        let result = semantic_tokens(&db, file_id);

        let has_string = result
            .data
            .iter()
            .any(|t| t.kind == SemanticTokenKind::String);
        assert!(has_string, "should have String tokens");
    }

    #[test]
    fn semantic_tokens_classifies_number_literals() {
        let (db, file_id) = setup_db("fn main() { x = 42 }");
        let result = semantic_tokens(&db, file_id);

        let has_number = result
            .data
            .iter()
            .any(|t| t.kind == SemanticTokenKind::Number);
        assert!(has_number, "should have Number tokens");
    }

    #[test]
    fn semantic_tokens_marks_definitions() {
        let (db, file_id) = setup_db("fn foo() {}");
        let result = semantic_tokens(&db, file_id);

        let has_definition = result.data.iter().any(|t| {
            t.kind == SemanticTokenKind::Function
                && t.modifiers.contains(&SemanticTokenModifier::Definition)
        });
        assert!(
            has_definition,
            "function definition should have Definition modifier"
        );
    }

    #[test]
    fn semantic_tokens_marks_declarations() {
        let (db, file_id) = setup_db("fn main() { x = 42 }");
        let result = semantic_tokens(&db, file_id);

        let has_declaration = result.data.iter().any(|t| {
            t.kind == SemanticTokenKind::Variable
                && t.modifiers.contains(&SemanticTokenModifier::Declaration)
        });
        assert!(
            has_declaration,
            "variable binding should have Declaration modifier"
        );
    }

    #[test]
    fn semantic_tokens_handles_empty_file() {
        let (db, file_id) = setup_db("");
        let result = semantic_tokens(&db, file_id);

        assert!(
            result.data.is_empty(),
            "empty file should produce no tokens"
        );
    }

    #[test]
    fn semantic_tokens_handles_parse_errors() {
        let (db, file_id) = setup_db("fn main( {");
        let result = semantic_tokens(&db, file_id);

        // Should still produce tokens for valid portions (e.g. the `fn` keyword)
        assert!(
            !result.data.is_empty(),
            "should produce tokens for valid portions despite parse errors"
        );
        let has_keyword = result
            .data
            .iter()
            .any(|t| t.kind == SemanticTokenKind::Keyword);
        assert!(has_keyword, "should have Keyword token for `fn`");
    }

    #[test]
    fn semantic_tokens_are_sorted_by_position() {
        let (db, file_id) = setup_db(
            r#"
fn foo() {}
fn bar() {}
"#,
        );
        let result = semantic_tokens(&db, file_id);

        // Tokens should be sorted by (lineno, col)
        for window in result.data.windows(2) {
            let a = &window[0];
            let b = &window[1];
            assert!(
                (a.span.start.lineno, a.span.start.col) <= (b.span.start.lineno, b.span.start.col),
                "tokens should be sorted by position: {:?} should come before {:?}",
                a,
                b
            );
        }
    }
}
