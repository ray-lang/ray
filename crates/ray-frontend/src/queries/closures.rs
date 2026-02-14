//! Closure analysis queries for the incremental compiler.

use ray_core::sema::closure::{self, ClosureInfo};
use ray_query_macros::query;
use ray_shared::{def::DefId, node_id::NodeId};

use crate::{
    queries::{defs::find_def_ast, resolve::name_resolutions, transform::file_ast},
    query::{Database, Query},
};

/// Analyze closures within a single definition.
///
/// Returns information about all closure expressions within the definition,
/// including which variables they capture from their enclosing scope.
///
/// # Arguments
///
/// * `db` - The query database
/// * `def_id` - The definition to analyze
///
/// # Returns
///
/// A vector of `ClosureInfo` structs, one for each closure expression in the
/// definition. Returns an empty vector if the definition contains no closures
/// or if the definition cannot be found.
#[query]
pub fn closures_in_def(db: &Database, def_id: DefId) -> Vec<ClosureInfo> {
    let file_result = file_ast(db, def_id.file);
    let resolutions = name_resolutions(db, def_id.file);

    // Find the DefHeader for this definition
    let def_header = match file_result.defs.iter().find(|h| h.def_id == def_id) {
        Some(header) => header,
        None => return Vec::new(),
    };

    // Find the AST node for this definition using root_node
    let def_ast = match find_def_ast(&file_result.ast.decls, def_header.root_node) {
        Some(ast) => ast,
        None => return Vec::new(),
    };

    closure::closures_in_def(def_id, def_ast, &resolutions)
}

/// Look up closure information for a specific closure expression.
///
/// Given a NodeId for a closure expression, returns the `ClosureInfo` for that
/// closure, including its captured variables.
///
/// # Arguments
///
/// * `db` - The query database
/// * `closure_node` - The NodeId of the closure expression
///
/// # Returns
///
/// `Some(ClosureInfo)` if the NodeId corresponds to a closure expression within
/// its owning definition, `None` otherwise.
#[query]
pub fn closure_info(db: &Database, closure_node: NodeId) -> Option<ClosureInfo> {
    let def_id = closure_node.owner;
    let closures = closures_in_def(db, def_id);
    closures
        .into_iter()
        .find(|c| c.closure_expr == closure_node)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::pathlib::{FilePath, ModulePath};

    use ray_shared::{def::DefId, node_id::NodeId};

    use crate::{
        queries::{
            closures::{closure_info, closures_in_def},
            libraries::LoadedLibraries,
            parse::parse_file,
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn closures_in_def_finds_closure_in_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with a closure that captures a local variable
        // Ray closure syntax: () => expr or arg => expr
        FileSource::new(
            &db,
            file_id,
            r#"
fn outer() {
    x = 42
    f = () => x + 1
    f()
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let closures = closures_in_def(&db, outer_def.def_id);

        assert_eq!(closures.len(), 1, "Should find 1 closure");
        let closure_info = &closures[0];
        assert_eq!(closure_info.parent_def, outer_def.def_id);
        // The closure captures 'x'
        assert!(
            !closure_info.captures.is_empty(),
            "Closure should capture x"
        );
    }

    #[test]
    fn closures_in_def_finds_closure_without_captures() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with a closure that doesn't capture anything
        FileSource::new(
            &db,
            file_id,
            r#"
fn outer() {
    f = () => 42
    f()
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let closures = closures_in_def(&db, outer_def.def_id);

        assert_eq!(closures.len(), 1, "Should find 1 closure");
        let closure_info = &closures[0];
        assert!(
            closure_info.captures.is_empty(),
            "Closure should not capture anything"
        );
    }

    #[test]
    fn closures_in_def_finds_multiple_closures() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with multiple closures
        FileSource::new(
            &db,
            file_id,
            r#"
fn outer() {
    x = 1
    y = 2
    f = () => x
    g = () => y
    f() + g()
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let closures = closures_in_def(&db, outer_def.def_id);

        assert_eq!(closures.len(), 2, "Should find 2 closures");
    }

    #[test]
    fn closures_in_def_returns_empty_for_function_without_closures() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with no closures
        FileSource::new(
            &db,
            file_id,
            r#"
fn simple(x: int) -> int { x + 1 }
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let simple_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "simple")
            .expect("should find simple function");

        let closures = closures_in_def(&db, simple_def.def_id);

        assert!(closures.is_empty(), "Should find no closures");
    }

    #[test]
    fn closures_in_def_returns_empty_for_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let point_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Point")
            .expect("should find Point struct");

        let closures = closures_in_def(&db, point_def.def_id);

        assert!(closures.is_empty(), "Struct should have no closures");
    }

    #[test]
    fn closures_in_def_returns_empty_for_unknown_def() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn foo() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        // Create a fake DefId that doesn't exist
        let fake_def_id = ray_shared::def::DefId {
            file: file_id,
            index: 999,
        };

        let closures = closures_in_def(&db, fake_def_id);

        assert!(closures.is_empty(), "Unknown def should return empty vec");
    }

    #[test]
    fn closure_info_returns_info_for_valid_closure_node() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with a closure
        FileSource::new(
            &db,
            file_id,
            r#"
fn outer() {
    x = 42
    f = () => x + 1
    f()
}
"#
            .to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        // First get the closure via closures_in_def to get its NodeId
        let closures = closures_in_def(&db, outer_def.def_id);
        assert_eq!(closures.len(), 1, "Should find 1 closure");

        let closure_node_id = closures[0].closure_expr;

        // Now look up via closure_info
        let info = closure_info(&db, closure_node_id);
        assert!(
            info.is_some(),
            "closure_info should return Some for valid closure"
        );

        let info = info.unwrap();
        assert_eq!(info.closure_expr, closure_node_id);
        assert_eq!(info.parent_def, outer_def.def_id);
        assert!(!info.captures.is_empty(), "Closure should capture x");
    }

    #[test]
    fn closure_info_returns_none_for_non_closure_node() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn foo() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        // Create a fake NodeId that doesn't correspond to a closure
        let fake_def_id = DefId {
            file: file_id,
            index: 0,
        };
        let fake_node_id = NodeId {
            owner: fake_def_id,
            index: 9999,
        };

        let info = closure_info(&db, fake_node_id);
        assert!(
            info.is_none(),
            "closure_info should return None for non-closure node"
        );
    }

    #[test]
    fn closure_info_returns_none_for_unknown_owner() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn foo() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        // Create a NodeId with a non-existent owner DefId
        let fake_def_id = DefId {
            file: file_id,
            index: 999,
        };
        let fake_node_id = NodeId {
            owner: fake_def_id,
            index: 1,
        };

        let info = closure_info(&db, fake_node_id);
        assert!(
            info.is_none(),
            "closure_info should return None for unknown owner"
        );
    }
}
