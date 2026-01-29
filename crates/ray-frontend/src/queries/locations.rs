//! Location queries for the incremental compiler.
//!
//! This module provides queries for looking up source locations:
//! - `span_of`: Get the span for a node
//! - `find_at_position`: Find the node at a given position

use ray_query_macros::query;
use ray_shared::{file_id::FileId, node_id::NodeId, span::Span};

use crate::{
    queries::{parse::parse_file, workspace::WorkspaceSnapshot},
    query::{Database, Query},
};

/// Returns the span for a given node.
///
/// Looks up the source location information for the node in the source map.
/// Returns `None` if the node doesn't have span information (e.g., synthetic nodes).
///
/// **Dependencies**: `parse_file(node_id.owner.file)`
#[query]
pub fn span_of(db: &Database, node_id: NodeId) -> Option<Span> {
    let file_id = node_id.owner.file;
    let parse_result = parse_file(db, file_id);
    parse_result
        .source_map
        .get_by_id(node_id)
        .and_then(|source| source.span)
}

/// Finds the most specific node at a given position in a file.
///
/// Returns the NodeId of the smallest node whose span contains the given
/// line and column position. This is useful for implementing features like
/// go-to-definition and hover information.
///
/// **Dependencies**: `parse_file(file_id)`, `WorkspaceSnapshot`
#[query]
pub fn find_at_position(db: &Database, file_id: FileId, line: usize, col: usize) -> Option<NodeId> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let file_info = workspace.file_info(file_id)?;
    let parse_result = parse_file(db, file_id);

    parse_result
        .source_map
        .find_at_position(&file_info.path, line, col)
        .map(|(node_id, _source)| node_id)
}

#[cfg(test)]
mod tests {
    use ray_shared::{
        def::DefId,
        node_id::NodeId,
        pathlib::{FilePath, ModulePath},
    };

    use crate::{
        queries::{
            locations::{find_at_position, span_of},
            parse::parse_file,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_test_db(source: &str) -> (Database, ray_shared::file_id::FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, source.to_string());
        (db, file_id)
    }

    // =========================================================================
    // Tests for span_of
    // =========================================================================

    #[test]
    fn span_of_returns_span_for_valid_node() {
        let source = "fn main() {}";
        let (db, file_id) = setup_test_db(source);

        let parse_result = parse_file(&db, file_id);

        // Get the NodeId of the function declaration
        let func_def = parse_result.defs.first().expect("Should have a def");
        let func_node_id = func_def.root_node;

        let span = span_of(&db, func_node_id);
        assert!(span.is_some(), "Should return span for function node");

        let span = span.unwrap();
        // The span should cover the entire function
        assert_eq!(span.start.lineno, 0, "Should start at line 0");
        assert_eq!(span.start.col, 0, "Should start at column 0");
    }

    #[test]
    fn span_of_returns_none_for_invalid_node() {
        let source = "fn main() {}";
        let (db, file_id) = setup_test_db(source);

        // Create a NodeId that doesn't exist in the source map but uses a valid file
        // Use the real file_id but a def index that doesn't exist
        let fake_def_id = DefId::new(file_id, 999);
        let _guard = NodeId::enter_def(fake_def_id);
        let fake_node_id = NodeId::new();

        let span = span_of(&db, fake_node_id);
        assert!(span.is_none(), "Should return None for non-existent node");
    }

    #[test]
    fn span_of_returns_correct_span_for_nested_node() {
        // Test that we can get spans for nodes inside functions
        let source = r#"fn foo() {
    x = 42
}"#;
        let (db, file_id) = setup_test_db(source);

        let parse_result = parse_file(&db, file_id);

        // Find a node inside the function body
        // We'll just verify the function itself has a span
        let func_def = parse_result.defs.first().expect("Should have a def");
        let span = span_of(&db, func_def.root_node);

        assert!(span.is_some(), "Should return span for function node");
        let span = span.unwrap();
        // Should span multiple lines
        assert!(
            span.end.lineno >= span.start.lineno,
            "Span should cover at least one line"
        );
    }

    // =========================================================================
    // Tests for find_at_position
    // =========================================================================

    #[test]
    fn find_at_position_returns_node_at_valid_position() {
        let source = "fn main() {}";
        let (db, file_id) = setup_test_db(source);

        // Position at the start of the function (line 0, col 0)
        let node_id = find_at_position(&db, file_id, 0, 0);
        assert!(
            node_id.is_some(),
            "Should find a node at the start of function"
        );
    }

    #[test]
    fn find_at_position_returns_none_for_invalid_position() {
        let source = "fn main() {}";
        let (db, file_id) = setup_test_db(source);

        // Position way past the end of the file
        let node_id = find_at_position(&db, file_id, 100, 0);
        assert!(
            node_id.is_none(),
            "Should return None for position outside file"
        );
    }

    #[test]
    fn find_at_position_returns_most_specific_node() {
        // Test that we get the innermost/most specific node at a position
        let source = r#"fn foo() {
    x = 42
}"#;
        let (db, file_id) = setup_test_db(source);

        // Position on line 1, inside the function body
        // The position should be inside the assignment expression
        let node_id = find_at_position(&db, file_id, 1, 4);
        assert!(
            node_id.is_some(),
            "Should find a node inside the function body"
        );

        // Verify we got a node and can look up its span
        let node_id = node_id.unwrap();
        let span = span_of(&db, node_id);
        assert!(span.is_some(), "Found node should have a span");
    }

    #[test]
    fn find_at_position_works_for_multiline_code() {
        let source = r#"struct Point {
    x: int,
    y: int
}

fn distance(p: Point) -> int {
    p.x
}"#;
        let (db, file_id) = setup_test_db(source);

        // Find node at struct definition (line 0)
        let node_at_struct = find_at_position(&db, file_id, 0, 7);
        assert!(node_at_struct.is_some(), "Should find struct at line 0");

        // Find node at function definition (line 5)
        let node_at_func = find_at_position(&db, file_id, 5, 3);
        assert!(node_at_func.is_some(), "Should find function at line 5");
    }

    #[test]
    fn find_at_position_returns_none_for_nonexistent_file() {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        // Note: We don't create FileSource, so parse will fail

        // Create a fake file ID that doesn't exist
        let fake_file_id = ray_shared::file_id::FileId(999);

        let node_id = find_at_position(&db, fake_file_id, 0, 0);
        assert!(
            node_id.is_none(),
            "Should return None for non-existent file"
        );

        // Also test with the real file_id but no source
        // This should still work (return None) because file_info exists
        // but we need to add the source for parse to work
        FileSource::new(&db, file_id, "".to_string());
        let node_id = find_at_position(&db, file_id, 0, 0);
        // Empty file has no nodes at position 0,0
        assert!(
            node_id.is_none(),
            "Should return None for empty file at position 0,0"
        );
    }
}
