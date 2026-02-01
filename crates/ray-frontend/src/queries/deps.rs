use std::collections::HashMap;

use ray_query_macros::query;
use ray_shared::{
    def::{DefHeader, DefId, DefKind, SignatureStatus},
    pathlib::ModulePath,
    resolution::{DefTarget, Resolution},
};
use ray_typing::binding_groups::BindingGraph;

use crate::{
    queries::{parse::parse_file, resolve, workspace::WorkspaceSnapshot},
    query::{Database, Query},
};

/// Identifies a binding group within a module.
///
/// Using a compact ID rather than Vec<DefId> as the query key ensures that:
/// - The key is hashable and cheap to compare
/// - The query system can efficiently track dependencies
///
/// Note: BindingGroupId is stable within a given `binding_groups(module)` result,
/// but the index may change if the binding graph changes (e.g., due to edits
/// that add/remove definitions or change dependencies).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BindingGroupId {
    pub module: ModulePath,
    pub index: u32, // SCC index in topological order
}

/// Result of computing binding groups for a module.
///
/// Contains both the group IDs and the actual members, allowing
/// `binding_group_members` to do a direct lookup by index.
#[derive(Clone, Debug)]
pub struct BindingGroupsResult {
    /// Group IDs in topological order (dependencies before dependents).
    pub group_ids: Vec<BindingGroupId>,
    /// Members of each group, indexed by group index.
    /// `members[i]` contains the DefIds for `group_ids[i]`.
    pub members: Vec<Vec<DefId>>,
}

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

/// Determines whether a definition is "unannotated" for binding graph purposes.
///
/// All definitions go through type inference - there are no exceptions. This function
/// determines whether edges TO this definition should be included in the binding graph.
///
/// Edges to unannotated definitions are included because the caller and callee must be
/// inferred *together* (potentially in the same SCC). Edges to annotated definitions
/// are omitted because the callee's type is already known - there's no need to infer
/// them together.
///
/// Unannotated definitions:
/// - `DefKind::FileMain`: Top-level expressions
/// - `DefKind::Function { signature: Unannotated }`: Missing parameter/return annotations
/// - `DefKind::Binding { annotated: false, .. }`: Unannotated let binding
/// - `DefKind::AssociatedConst { annotated: false }`: Unannotated associated const
///
/// Annotated definitions (edges omitted):
/// - Structs, traits, impls, type aliases (always have explicit types)
/// - Methods (always have explicit signature from trait or explicit)
/// - Functions with `FullyAnnotated` or `ReturnElided` signature status
fn is_unannotated(kind: DefKind) -> bool {
    match kind {
        DefKind::FileMain => true,
        // Only Unannotated functions create inference edges
        // FullyAnnotated and ReturnElided are both considered "annotated"
        DefKind::Function { signature } => signature == SignatureStatus::Unannotated,
        DefKind::Binding { annotated, .. } => !annotated,
        DefKind::AssociatedConst { annotated } => !annotated,
        // These definitions have explicit types - edges to them are omitted
        DefKind::Method
        | DefKind::Struct
        | DefKind::Trait
        | DefKind::Impl
        | DefKind::TypeAlias
        | DefKind::Primitive => false,
    }
}

/// Build the binding graph for a module.
///
/// The binding graph determines which definitions must be type-inferred *together*
/// (in the same SCC). All definitions go through type inference - there are no
/// exceptions. The graph determines grouping, not whether inference happens.
///
/// An edge A → B is included only if B is unannotated. Edges to annotated
/// definitions are omitted because their types are already known - there's no
/// need to infer A and B together.
///
/// All definitions in the module are nodes in the graph, but only edges
/// to unannotated definitions are included. This means annotated definitions
/// that only reference other annotated definitions become singleton SCCs.
#[query]
pub fn binding_graph(db: &Database, module: ModulePath) -> BindingGraph<DefId> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let module_info = match workspace.module_info(&module) {
        Some(info) => info,
        None => return BindingGraph::new(),
    };

    // Collect all def headers from all files in the module
    // Build a lookup map for filtering edges
    let mut def_kinds: HashMap<DefId, DefKind> = HashMap::new();
    let mut all_defs: Vec<DefHeader> = Vec::new();

    for &file_id in &module_info.files {
        let parse_result = parse_file(db, file_id);
        for def_header in parse_result.defs {
            def_kinds.insert(def_header.def_id, def_header.kind);
            all_defs.push(def_header);
        }
    }

    // Build the binding graph with filtered edges
    let mut graph = BindingGraph::new();

    for def_header in &all_defs {
        // Add the definition as a node (even if it has no edges)
        graph.add_binding(def_header.def_id);

        // Get raw dependencies
        let deps = def_deps(db, def_header.def_id);

        // Filter edges: only include edges to unannotated definitions
        // Edges to annotated defs are omitted - their types are already known
        for dep in deps {
            if let Some(&dep_kind) = def_kinds.get(&dep) {
                if is_unannotated(dep_kind) {
                    graph.add_edge(def_header.def_id, dep);
                }
            }
            // Note: If dep is not in def_kinds, it's a cross-module reference.
            // Cross-module references are excluded from the binding graph
            // since they don't participate in the same SCC computation.
        }
    }

    graph
}

/// Compute binding groups for a module.
///
/// Binding groups are the strongly connected components (SCCs) of the binding graph.
/// Definitions within the same SCC must be type-inferred together because they may
/// reference each other.
///
/// Returns group IDs in topological order: dependencies come before dependents.
/// Every definition in the module appears in exactly one group.
#[query]
pub fn binding_groups(db: &Database, module: ModulePath) -> BindingGroupsResult {
    let graph = binding_graph(db, module.clone());
    let sccs = graph.compute_binding_groups(); // Tarjan's algorithm

    let group_ids: Vec<BindingGroupId> = (0..sccs.len())
        .map(|idx| BindingGroupId {
            module: module.clone(),
            index: idx as u32,
        })
        .collect();

    let members: Vec<Vec<DefId>> = sccs.into_iter().map(|group| group.bindings).collect();

    BindingGroupsResult { group_ids, members }
}

/// Get the members of a binding group.
///
/// Returns the DefIds belonging to the specified binding group. For singleton
/// groups (annotated definitions with no unannotated dependencies), returns
/// a single DefId.
#[query]
pub fn binding_group_members(db: &Database, group_id: BindingGroupId) -> Vec<DefId> {
    let result = binding_groups(db, group_id.module.clone());
    result
        .members
        .get(group_id.index as usize)
        .cloned()
        .unwrap_or_default()
}

/// Get the binding group containing a definition.
///
/// Returns the binding group that contains the given definition. This is the
/// inverse of `binding_group_members`.
///
/// # Panics
///
/// Panics if the DefId is not found in any group. This is an internal error -
/// every definition should be in exactly one group.
#[query]
pub fn binding_group_for_def(db: &Database, def_id: DefId) -> BindingGroupId {
    // Get the module for this definition's file
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let file_info = workspace
        .file_info(def_id.file)
        .expect("file not in workspace");
    let module = file_info.module_path.clone();

    // Get the binding groups for this module
    let result = binding_groups(db, module);

    // Find which group contains this def
    for (idx, members) in result.members.iter().enumerate() {
        if members.contains(&def_id) {
            return result.group_ids[idx].clone();
        }
    }

    panic!(
        "DefId {:?} not found in any binding group (internal error)",
        def_id
    );
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            deps::{
                BindingGroupId, binding_graph, binding_group_for_def, binding_group_members,
                binding_groups, def_deps,
            },
            libraries::LoadedLibraries,
            parse::parse_file,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
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

    // ==================== binding_graph tests ====================

    #[test]
    fn binding_graph_includes_all_defs_as_nodes() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
fn foo() -> int { 1 }
fn bar() -> int { 2 }
"#
            .to_string(),
        );

        let graph = binding_graph(&db, module_path);

        // Both functions should be nodes in the graph
        assert_eq!(graph.edges.len(), 2, "Should have 2 nodes in graph");
    }

    #[test]
    fn binding_graph_includes_edge_to_unannotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // caller calls helper, which has an unannotated parameter (truly unannotated)
        // Note: fn helper() { 42 } would be ReturnElided (params vacuously annotated),
        // but fn helper(x) { x } has an unannotated param so is Unannotated
        FileSource::new(
            &db,
            file_id,
            r#"
fn helper(x) {
    x
}

fn caller() -> int {
    helper(42)
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let helper_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "helper")
            .expect("should find helper");
        let caller_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "caller")
            .expect("should find caller");

        let graph = binding_graph(&db, module_path);

        // caller -> helper edge should exist (helper is truly unannotated)
        let caller_edges = graph
            .edges
            .get(&caller_def.def_id)
            .expect("caller in graph");
        assert!(
            caller_edges.contains(&helper_def.def_id),
            "caller should have edge to unannotated helper"
        );
    }

    #[test]
    fn binding_graph_excludes_edge_to_annotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // caller calls helper, which IS fully annotated
        FileSource::new(
            &db,
            file_id,
            r#"
fn helper() -> int {
    42
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
            .expect("should find helper");
        let caller_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "caller")
            .expect("should find caller");

        let graph = binding_graph(&db, module_path);

        // caller -> helper edge should NOT exist (helper is fully annotated)
        let caller_edges = graph
            .edges
            .get(&caller_def.def_id)
            .expect("caller in graph");
        assert!(
            !caller_edges.contains(&helper_def.def_id),
            "caller should NOT have edge to annotated helper"
        );

        // Both should still be nodes
        assert!(graph.edges.contains_key(&helper_def.def_id));
        assert!(graph.edges.contains_key(&caller_def.def_id));
    }

    #[test]
    fn binding_graph_excludes_edge_to_arrow_body_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // helper uses arrow body (=>) - this is ReturnElided status (annotated)
        // ReturnElided is considered "annotated" - no edge should exist
        FileSource::new(
            &db,
            file_id,
            r#"
fn helper() => 42

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
            .expect("should find helper");
        let caller_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "caller")
            .expect("should find caller");

        let graph = binding_graph(&db, module_path);

        // caller -> helper edge should NOT exist (arrow body = ReturnElided = annotated)
        let caller_edges = graph
            .edges
            .get(&caller_def.def_id)
            .expect("caller in graph");
        assert!(
            !caller_edges.contains(&helper_def.def_id),
            "caller should NOT have edge to arrow-body helper (ReturnElided)"
        );
    }

    #[test]
    fn binding_graph_includes_edge_to_block_body_missing_return() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // helper uses block body {} without return annotation - this is Unannotated
        // (params are vacuously annotated, but missing return type with block = unannotated)
        FileSource::new(
            &db,
            file_id,
            r#"
fn helper() {
    42
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
            .expect("should find helper");
        let caller_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "caller")
            .expect("should find caller");

        let graph = binding_graph(&db, module_path);

        // caller -> helper edge SHOULD exist (block body without return = Unannotated)
        let caller_edges = graph
            .edges
            .get(&caller_def.def_id)
            .expect("caller in graph");
        assert!(
            caller_edges.contains(&helper_def.def_id),
            "caller should have edge to block-body helper without return annotation (Unannotated)"
        );
    }

    #[test]
    fn binding_graph_excludes_edge_to_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // make_point references Point struct
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
            .expect("should find Point");
        let make_point_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "make_point")
            .expect("should find make_point");

        let graph = binding_graph(&db, module_path);

        // make_point -> Point edge should NOT exist (structs are never inference targets)
        let make_point_edges = graph
            .edges
            .get(&make_point_def.def_id)
            .expect("make_point in graph");
        assert!(
            !make_point_edges.contains(&point_def.def_id),
            "make_point should NOT have edge to struct Point"
        );
    }

    #[test]
    fn binding_graph_mutual_recursion_forms_scc() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // is_even and is_odd are mutually recursive and unannotated
        FileSource::new(
            &db,
            file_id,
            r#"
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let is_even_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_even")
            .expect("should find is_even");
        let is_odd_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_odd")
            .expect("should find is_odd");

        let graph = binding_graph(&db, module_path);

        // Both should have edges to each other (mutual recursion between unannotated functions)
        let is_even_edges = graph
            .edges
            .get(&is_even_def.def_id)
            .expect("is_even in graph");
        let is_odd_edges = graph
            .edges
            .get(&is_odd_def.def_id)
            .expect("is_odd in graph");

        assert!(
            is_even_edges.contains(&is_odd_def.def_id),
            "is_even should have edge to is_odd"
        );
        assert!(
            is_odd_edges.contains(&is_even_def.def_id),
            "is_odd should have edge to is_even"
        );

        // Compute SCCs - they should be in the same group
        let groups = graph.compute_binding_groups();
        let is_even_group = groups
            .iter()
            .position(|g| g.bindings.contains(&is_even_def.def_id))
            .expect("is_even in some group");
        let is_odd_group = groups
            .iter()
            .position(|g| g.bindings.contains(&is_odd_def.def_id))
            .expect("is_odd in some group");

        assert_eq!(
            is_even_group, is_odd_group,
            "is_even and is_odd should be in the same SCC"
        );
    }

    #[test]
    fn binding_graph_returns_empty_for_unknown_module() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        let graph = binding_graph(&db, ModulePath::from("nonexistent"));

        assert!(
            graph.edges.is_empty(),
            "Unknown module should have empty graph"
        );
    }

    // ==================== binding_groups tests ====================

    #[test]
    fn binding_groups_returns_correct_group_ids() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Two independent annotated functions -> two singleton groups
        FileSource::new(
            &db,
            file_id,
            r#"
fn foo() -> int { 1 }
fn bar() -> int { 2 }
"#
            .to_string(),
        );

        let result = binding_groups(&db, module_path.clone());

        // Should have 2 groups
        assert_eq!(result.group_ids.len(), 2, "Should have 2 binding groups");
        assert_eq!(result.members.len(), 2, "Should have 2 member lists");

        // All group IDs should have correct module
        for group_id in &result.group_ids {
            assert_eq!(group_id.module, module_path);
        }

        // Indices should be sequential
        for (i, group_id) in result.group_ids.iter().enumerate() {
            assert_eq!(group_id.index, i as u32);
        }
    }

    #[test]
    fn binding_groups_singleton_for_annotated_functions() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Two annotated functions that call each other
        // Since both are annotated, no inference edges -> each is a singleton
        FileSource::new(
            &db,
            file_id,
            r#"
fn foo() -> int { bar() }
fn bar() -> int { foo() }
"#
            .to_string(),
        );

        let result = binding_groups(&db, module_path);

        // Each function should be in its own group (singleton SCCs)
        assert_eq!(result.group_ids.len(), 2, "Should have 2 singleton groups");
        for members in &result.members {
            assert_eq!(members.len(), 1, "Each group should have 1 member");
        }
    }

    #[test]
    fn binding_groups_mutual_recursion_same_group() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Mutually recursive unannotated functions
        FileSource::new(
            &db,
            file_id,
            r#"
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let is_even_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_even")
            .expect("should find is_even");
        let is_odd_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_odd")
            .expect("should find is_odd");

        let result = binding_groups(&db, module_path);

        // Should have exactly 1 group with both functions
        assert_eq!(
            result.group_ids.len(),
            1,
            "Should have 1 group for mutual recursion"
        );
        assert_eq!(result.members.len(), 1);

        let members = &result.members[0];
        assert_eq!(members.len(), 2, "Group should have 2 members");
        assert!(members.contains(&is_even_def.def_id));
        assert!(members.contains(&is_odd_def.def_id));
    }

    #[test]
    fn binding_groups_topological_order() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // caller depends on helper (unannotated), helper has no deps
        // Topological order: helper's group before caller's group
        FileSource::new(
            &db,
            file_id,
            r#"
fn helper(x) { x }

fn caller(y) { helper(y) }
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let helper_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "helper")
            .expect("should find helper");
        let caller_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "caller")
            .expect("should find caller");

        let result = binding_groups(&db, module_path);

        // Find which group each def is in
        let helper_group_idx = result
            .members
            .iter()
            .position(|m| m.contains(&helper_def.def_id))
            .expect("helper should be in a group");
        let caller_group_idx = result
            .members
            .iter()
            .position(|m| m.contains(&caller_def.def_id))
            .expect("caller should be in a group");

        // Dependencies come before dependents in topological order
        assert!(
            helper_group_idx < caller_group_idx,
            "helper's group (idx {}) should come before caller's group (idx {})",
            helper_group_idx,
            caller_group_idx
        );
    }

    #[test]
    fn binding_groups_every_def_in_exactly_one_group() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
struct Point { x: int, y: int }
fn make_point() -> Point { Point { x: 1, y: 2 } }
fn helper(x) { x }
fn caller() -> int { helper(42) }
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let result = binding_groups(&db, module_path);

        // Flatten all members
        let all_members: Vec<_> = result.members.iter().flatten().copied().collect();

        // Every def from parse should appear exactly once
        for def_header in &parse_result.defs {
            let count = all_members
                .iter()
                .filter(|&&id| id == def_header.def_id)
                .count();
            assert_eq!(
                count, 1,
                "Def {} should appear exactly once, but appeared {} times",
                def_header.name, count
            );
        }

        // Total members should equal total defs
        assert_eq!(
            all_members.len(),
            parse_result.defs.len(),
            "Total members should equal total defs"
        );
    }

    #[test]
    fn binding_groups_returns_empty_for_unknown_module() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        let result = binding_groups(&db, ModulePath::from("nonexistent"));

        assert!(result.group_ids.is_empty());
        assert!(result.members.is_empty());
    }

    #[test]
    fn binding_groups_group_id_can_be_used_as_key() {
        // Test that BindingGroupId is usable as a HashMap key
        let module = ModulePath::from("test");
        let id1 = BindingGroupId {
            module: module.clone(),
            index: 0,
        };
        let id2 = BindingGroupId {
            module: module.clone(),
            index: 1,
        };
        let id1_copy = BindingGroupId {
            module: module.clone(),
            index: 0,
        };

        let mut set = HashSet::new();
        set.insert(id1);
        set.insert(id2);
        set.insert(id1_copy); // Should not add duplicate

        assert_eq!(set.len(), 2);
        assert!(set.contains(&BindingGroupId { module, index: 0 }));
    }

    // ==================== binding_group_members tests ====================

    #[test]
    fn binding_group_members_returns_members_for_valid_group() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
fn foo() -> int { 1 }
fn bar() -> int { 2 }
"#
            .to_string(),
        );

        let groups_result = binding_groups(&db, module_path.clone());

        // Query each group's members
        for (i, group_id) in groups_result.group_ids.iter().enumerate() {
            let members = binding_group_members(&db, group_id.clone());
            assert_eq!(
                members, groups_result.members[i],
                "binding_group_members should return same members as BindingGroupsResult"
            );
        }
    }

    #[test]
    fn binding_group_members_returns_singleton_for_annotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
fn annotated() -> int { 42 }
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let annotated_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "annotated")
            .expect("should find annotated");

        let groups_result = binding_groups(&db, module_path.clone());
        assert_eq!(groups_result.group_ids.len(), 1);

        let members = binding_group_members(&db, groups_result.group_ids[0].clone());
        assert_eq!(members.len(), 1, "Annotated function should be singleton");
        assert_eq!(members[0], annotated_def.def_id);
    }

    #[test]
    fn binding_group_members_returns_multiple_for_mutual_recursion() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let is_even_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_even")
            .expect("should find is_even");
        let is_odd_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_odd")
            .expect("should find is_odd");

        let groups_result = binding_groups(&db, module_path.clone());
        assert_eq!(
            groups_result.group_ids.len(),
            1,
            "Should have 1 group for mutual recursion"
        );

        let members = binding_group_members(&db, groups_result.group_ids[0].clone());
        assert_eq!(members.len(), 2, "Group should have 2 members");
        assert!(members.contains(&is_even_def.def_id));
        assert!(members.contains(&is_odd_def.def_id));
    }

    #[test]
    fn binding_group_members_returns_empty_for_invalid_index() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn foo() -> int { 1 }".to_string());

        // Create a group ID with an invalid index
        let invalid_group_id = BindingGroupId {
            module: module_path,
            index: 999,
        };

        let members = binding_group_members(&db, invalid_group_id);
        assert!(members.is_empty(), "Invalid index should return empty vec");
    }

    #[test]
    fn binding_group_members_returns_empty_for_unknown_module() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        let group_id = BindingGroupId {
            module: ModulePath::from("nonexistent"),
            index: 0,
        };

        let members = binding_group_members(&db, group_id);
        assert!(members.is_empty(), "Unknown module should return empty vec");
    }

    // ==================== binding_group_for_def tests ====================

    #[test]
    fn binding_group_for_def_returns_correct_group() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
fn foo() -> int { 1 }
fn bar() -> int { 2 }
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

        let foo_group = binding_group_for_def(&db, foo_def.def_id);
        let bar_group = binding_group_for_def(&db, bar_def.def_id);

        // Both should have correct module
        assert_eq!(foo_group.module, module_path);
        assert_eq!(bar_group.module, module_path);

        // They should be in different groups (both are annotated, no edges between them)
        assert_ne!(foo_group.index, bar_group.index);
    }

    #[test]
    fn binding_group_for_def_returns_same_group_for_mutual_recursion() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);
        let is_even_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_even")
            .expect("should find is_even");
        let is_odd_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "is_odd")
            .expect("should find is_odd");

        let is_even_group = binding_group_for_def(&db, is_even_def.def_id);
        let is_odd_group = binding_group_for_def(&db, is_odd_def.def_id);

        // Both should be in the same group
        assert_eq!(is_even_group, is_odd_group);
    }

    #[test]
    fn binding_group_for_def_is_inverse_of_binding_group_members() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(
            &db,
            file_id,
            r#"
struct Point { x: int, y: int }
fn make_point() -> Point { Point { x: 1, y: 2 } }
fn helper(x) { x }
fn caller() -> int { helper(42) }
"#
            .to_string(),
        );

        let parse_result = parse_file(&db, file_id);

        // For every def, binding_group_for_def should return a group that contains that def
        for def_header in &parse_result.defs {
            let group_id = binding_group_for_def(&db, def_header.def_id);
            let members = binding_group_members(&db, group_id);
            assert!(
                members.contains(&def_header.def_id),
                "binding_group_members should contain the def that was used to find the group"
            );
        }
    }

    #[test]
    #[should_panic(expected = "not found in any binding group")]
    fn binding_group_for_def_panics_for_unknown_def() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn foo() -> int { 1 }".to_string());

        // Create a DefId that doesn't exist in the module
        let fake_def_id = ray_shared::def::DefId {
            file: file_id,
            index: 9999,
        };

        // This should panic
        binding_group_for_def(&db, fake_def_id);
    }
}
