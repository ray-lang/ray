use ray_query_macros::query;
use ray_shared::{
    def::DefId,
    resolution::{DefTarget, Resolution},
};

use crate::{
    queries::resolve,
    query::{Database, Query},
};

/// Extract the definition dependencies for a single definition.
///
/// Returns the list of workspace DefIds that this definition references.
/// This is used to build the dependency graph for incremental compilation.
///
/// Only returns `DefTarget::Workspace` dependencies - library references are filtered out
/// since library definitions don't participate in binding analysis.
#[query]
pub fn def_deps(db: &Database, def_id: DefId) -> Vec<DefId> {
    let resolutions = resolve::name_resolutions(db, def_id.file);
    resolutions
        .iter()
        .filter(|(node_id, _)| node_id.owner == def_id)
        .filter_map(|(_, res)| match res {
            Resolution::Def(DefTarget::Workspace(target)) => Some(*target),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            deps::def_deps,
            libraries::LoadedLibraries,
            parse::parse_file,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new());
    }

    #[test]
    fn def_deps_returns_empty_for_function_with_no_deps() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with no references to other definitions
        FileSource::new(
            &db,
            file_id,
            r#"
fn standalone() -> int {
    42
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let standalone_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "standalone")
            .expect("should find standalone function");

        let deps = def_deps(&db, standalone_def.def_id);

        assert!(
            deps.is_empty(),
            "Function with no deps should return empty vec"
        );
    }

    #[test]
    fn def_deps_finds_function_dependency() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // caller depends on helper
        FileSource::new(
            &db,
            file_id,
            r#"
fn helper() -> int {
    1
}

fn caller() -> int {
    helper()
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let helper_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "helper")
            .expect("should find helper function");
        let caller_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "caller")
            .expect("should find caller function");

        let deps = def_deps(&db, caller_def.def_id);

        assert_eq!(deps.len(), 1, "caller should have exactly one dependency");
        assert_eq!(deps[0], helper_def.def_id, "caller should depend on helper");
    }

    #[test]
    fn def_deps_finds_struct_dependency() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // make_point depends on Point struct
        FileSource::new(
            &db,
            file_id,
            r#"
struct Point { x: int, y: int }

fn make_point() {
    p = Point { x: 1, y: 2 }
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let point_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "Point")
            .expect("should find Point struct");
        let make_point_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "make_point")
            .expect("should find make_point function");

        let deps = def_deps(&db, make_point_def.def_id);

        assert!(
            deps.contains(&point_def.def_id),
            "make_point should depend on Point struct"
        );
    }

    #[test]
    fn def_deps_finds_multiple_dependencies() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // main depends on both foo and bar
        FileSource::new(
            &db,
            file_id,
            r#"
fn foo() -> int { 1 }
fn bar() -> int { 2 }

fn main() -> int {
    foo() + bar()
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let foo_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "foo")
            .expect("should find foo");
        let bar_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "bar")
            .expect("should find bar");
        let main_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "main")
            .expect("should find main");

        let deps = def_deps(&db, main_def.def_id);

        assert_eq!(deps.len(), 2, "main should have two dependencies");
        assert!(deps.contains(&foo_def.def_id), "main should depend on foo");
        assert!(deps.contains(&bar_def.def_id), "main should depend on bar");
    }

    #[test]
    fn def_deps_excludes_local_variables() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with local variable - should not create dependency
        FileSource::new(
            &db,
            file_id,
            r#"
fn with_local() -> int {
    x = 42
    x
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let with_local_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "with_local")
            .expect("should find with_local function");

        let deps = def_deps(&db, with_local_def.def_id);

        assert!(
            deps.is_empty(),
            "Local variable references should not create dependencies"
        );
    }

    #[test]
    fn def_deps_excludes_parameters() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with parameter reference - should not create dependency
        FileSource::new(
            &db,
            file_id,
            r#"
fn identity(x: int) -> int {
    x
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let identity_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "identity")
            .expect("should find identity function");

        let deps = def_deps(&db, identity_def.def_id);

        assert!(
            deps.is_empty(),
            "Parameter references should not create dependencies"
        );
    }
}
