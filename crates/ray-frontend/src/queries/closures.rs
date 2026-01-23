//! Closure analysis queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::{
    ast::{Decl, Node},
    passes::closure::{self, ClosureInfo},
};
use ray_query_macros::query;
use ray_shared::{def::DefId, node_id::NodeId, resolution::Resolution};

use crate::{
    queries::{resolve::name_resolutions, transform::file_ast},
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

    // Convert resolutions to the format expected by closure::closures_in_def
    let resolutions_map: HashMap<NodeId, Resolution> = resolutions;

    closure::closures_in_def(def_id, def_ast, &resolutions_map)
}

/// Find a declaration AST node by its root NodeId.
///
/// Searches through declarations to find the one matching the given NodeId.
fn find_def_ast(decls: &[Node<Decl>], root_node: NodeId) -> Option<&Node<Decl>> {
    for decl in decls {
        // Check if this decl's node ID matches
        if decl.id == root_node {
            return Some(decl);
        }

        // Also check nested declarations (e.g., methods in impl blocks, trait methods)
        if let Some(nested) = find_nested_def(decl, root_node) {
            return Some(nested);
        }
    }

    None
}

/// Find a nested declaration within a parent declaration.
///
/// This handles cases like methods inside impl blocks or trait definitions.
fn find_nested_def(parent: &Node<Decl>, root_node: NodeId) -> Option<&Node<Decl>> {
    match &parent.value {
        Decl::Trait(tr) => {
            // Check methods in trait definition
            for field in &tr.fields {
                if field.id == root_node {
                    return Some(field);
                }
            }
        }
        _ => {}
    }
    None
}

#[cfg(test)]
mod tests {
    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            closures::closures_in_def,
            libraries::LoadedLibraries,
            parse::parse_file,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
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
        assert!(!closure_info.captures.is_empty(), "Closure should capture x");
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

        // Create a fake DefId that doesn't exist
        let fake_def_id = ray_shared::def::DefId {
            file: file_id,
            index: 999,
        };

        let closures = closures_in_def(&db, fake_def_id);

        assert!(closures.is_empty(), "Unknown def should return empty vec");
    }
}
