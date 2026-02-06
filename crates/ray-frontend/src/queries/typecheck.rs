//! TypecheckEnv implementation for the incremental query system.
//!
//! This module provides `QueryEnv`, which implements the `TypecheckEnv` trait
//! from ray-typing by delegating to the various definition lookup queries.
//! This bridges the gap between the typechecker core (which knows nothing about
//! the query system) and the incremental frontend (which uses queries for
//! definition lookups).

use std::collections::HashMap;

use ray_core::{
    ast::{Decl, Node},
    typing::build_typecheck_input,
};
use ray_query_macros::query;
use ray_shared::{
    def::DefId, file_id::FileId, local_binding::LocalBindingId, node_id::NodeId, pathlib::ItemPath,
    resolution::DefTarget, ty::Ty,
};
use ray_typing::{
    TypeCheckInput, TypeCheckResult,
    binding_groups::{BindingGraph, BindingGroup},
    env::TypecheckEnv,
    types::{ImplTy, StructTy, TraitTy, TyScheme},
};

use crate::{
    queries::{
        bindings::local_bindings_for_group,
        defs::{
            all_traits, def_for_path, def_path, impl_def, impls_for_trait, impls_for_type,
            struct_def, trait_def,
        },
        deps::{BindingGroupId, binding_graph, binding_group_for_def, binding_group_members},
        libraries::library_data,
        operators::{lookup_infix_op, lookup_prefix_op},
        resolve::{name_resolutions, resolve_builtin},
        transform::file_ast,
        types::annotated_scheme,
    },
    query::{Database, Query},
};

/// Query-based implementation of `TypecheckEnv`.
///
/// This struct holds a reference to the query database and provides
/// `TypecheckEnv` method implementations by calling the appropriate queries.
///
/// The `file_id` is used for context-dependent operations like `resolve_builtin`,
/// which needs to know what file's imports are in scope.
///
/// The `group_id` identifies the current binding group being typechecked,
/// used for `local_bindings_for_group`. This is optional because some contexts
/// (like AST lowering) don't have a binding group context.
pub struct QueryEnv<'db> {
    db: &'db Database,
    file_id: FileId,
    group_id: Option<BindingGroupId>,
}

impl<'db> QueryEnv<'db> {
    /// Create a new QueryEnv for a specific file context without a binding group.
    ///
    /// The file_id determines what imports are in scope for builtin resolution.
    /// Use `with_group` when you need `local_bindings_for_group` functionality.
    pub fn new(db: &'db Database, file_id: FileId) -> Self {
        QueryEnv {
            db,
            file_id,
            group_id: None,
        }
    }

    /// Create a new QueryEnv with a binding group context.
    ///
    /// The file_id determines what imports are in scope for builtin resolution.
    /// The group_id enables `local_bindings_for_group` to return bindings for the group.
    pub fn with_group(db: &'db Database, file_id: FileId, group_id: BindingGroupId) -> Self {
        QueryEnv {
            db,
            file_id,
            group_id: Some(group_id),
        }
    }
}

impl<'db> TypecheckEnv for QueryEnv<'db> {
    fn struct_def(&self, path: &ItemPath) -> Option<StructTy> {
        // Look up the DefTarget for this path
        let target = def_for_path(self.db, path.clone())?;

        // Get the struct definition and convert to StructTy
        Some(struct_def(self.db, target)?.convert_to_struct_ty())
    }

    fn trait_def(&self, path: &ItemPath) -> Option<TraitTy> {
        let target = def_for_path(self.db, path.clone())?;
        let trait_definition = trait_def(self.db, target)?;
        Some(trait_definition.convert_to_trait_ty())
    }

    fn all_traits(&self) -> Vec<TraitTy> {
        all_traits(self.db)
            .into_iter()
            .map(|trait_def| trait_def.convert_to_trait_ty())
            .collect()
    }

    fn impls_for_trait(&self, trait_path: &ItemPath) -> Vec<ImplTy> {
        let target = match def_for_path(self.db, trait_path.clone()) {
            Some(t) => t,
            None => return vec![],
        };

        let impl_targets = impls_for_trait(self.db, target);

        impl_targets
            .into_iter()
            .filter_map(|impl_target| Some(impl_def(self.db, impl_target)?.convert_to_impl_ty()))
            .collect()
    }

    fn inherent_impls(&self, type_path: &ItemPath) -> Vec<ImplTy> {
        let target = match def_for_path(self.db, type_path.clone()) {
            Some(t) => t,
            None => return vec![],
        };

        let impls_result = impls_for_type(self.db, target);

        impls_result
            .inherent
            .into_iter()
            .filter_map(|impl_target| Some(impl_def(self.db, impl_target)?.convert_to_impl_ty()))
            .collect()
    }

    fn impls_for_recv(&self, recv_path: &ItemPath) -> Vec<ImplTy> {
        let target = match def_for_path(self.db, recv_path.clone()) {
            Some(t) => t,
            None => return vec![],
        };

        let impls_result = impls_for_type(self.db, target);

        // Combine both inherent and trait impls
        impls_result
            .inherent
            .into_iter()
            .chain(impls_result.trait_impls.into_iter())
            .filter_map(|impl_target| Some(impl_def(self.db, impl_target)?.convert_to_impl_ty()))
            .collect()
    }

    fn external_scheme(&self, def_id: DefId) -> Option<TyScheme> {
        annotated_scheme(self.db, def_id)
    }

    fn resolve_builtin(&self, name: &str) -> ItemPath {
        // Try to resolve the builtin in the current file's scope
        match resolve_builtin(self.db, self.file_id, name.to_string()) {
            Some(target) => {
                def_path(self.db, target).expect("resolved builtin should have a valid path")
            }
            None => {
                // Fall back to core::{name}
                ItemPath::from(format!("core::{}", name).as_str())
            }
        }
    }

    fn infix_op(&self, symbol: &str) -> Option<(ItemPath, ItemPath)> {
        let entry = lookup_infix_op(self.db, symbol.to_string())?;

        // Convert DefTargets to ItemPaths
        let trait_path = def_path(self.db, entry.trait_def)?;
        let method_path = def_path(self.db, entry.method_def)?;

        Some((trait_path, method_path))
    }

    fn prefix_op(&self, symbol: &str) -> Option<(ItemPath, ItemPath)> {
        let entry = lookup_prefix_op(self.db, symbol.to_string())?;

        let trait_path = def_path(self.db, entry.trait_def)?;
        let method_path = def_path(self.db, entry.method_def)?;

        Some((trait_path, method_path))
    }

    fn external_local_type(&self, local_id: LocalBindingId) -> Option<Ty> {
        inferred_local_type(self.db, local_id)
    }

    fn def_item_path(&self, target: &DefTarget) -> Option<ItemPath> {
        def_path(self.db, target.clone())
    }

    fn local_bindings_for_group(&self) -> HashMap<NodeId, LocalBindingId> {
        match &self.group_id {
            Some(group_id) => local_bindings_for_group(self.db, group_id.clone()),
            None => HashMap::new(),
        }
    }
}

/// Lowers a single definition to typechecker IR.
///
/// For regular definitions (functions, structs, traits, impls), this finds
/// the declaration AST node and lowers it. For FileMain (DefKind::FileMain),
/// this lowers the file's top-level statements.
///
/// The returned `TypeCheckInput` contains an empty binding graph since
/// binding group construction is handled by a separate query.
#[query]
pub fn typecheck_def_input(db: &Database, def_id: DefId) -> TypeCheckInput {
    let file_result = file_ast(db, def_id.file);
    let resolutions = name_resolutions(db, def_id.file);
    let env = QueryEnv::new(db, def_id.file);

    // Find the def header for this def_id
    let def_header = file_result.defs.iter().find(|h| h.def_id == def_id);

    // Find the declaration AST node (works for both top-level and nested defs)
    if let Some(header) = def_header {
        if let Some(decl) = find_decl_by_id(&file_result.ast.decls, header.root_node) {
            return build_typecheck_input(
                &[decl.clone()],
                &[],
                &file_result.source_map,
                &env,
                &resolutions,
                BindingGraph::new(),
            );
        }
    }

    // Fallback: return empty input if def not found
    build_typecheck_input(
        &[],
        &[],
        &file_result.source_map,
        &env,
        &resolutions,
        BindingGraph::new(),
    )
}

/// Find a declaration AST node by its NodeId, searching both top-level
/// declarations and nested definitions inside impl blocks.
fn find_decl_by_id(decls: &[Node<Decl>], node_id: NodeId) -> Option<&Node<Decl>> {
    for decl in decls {
        // Check top-level declaration
        if decl.id == node_id {
            return Some(decl);
        }
        // Check nested declarations inside impl blocks
        if let Decl::Impl(im) = &decl.value {
            if let Some(funcs) = &im.funcs {
                if let Some(method) = funcs.iter().find(|d| d.id == node_id) {
                    return Some(method);
                }
            }
        }
    }
    None
}

/// Combines per-definition lowered inputs into a single `TypeCheckInput` for a binding group.
///
/// This query collects the `TypeCheckInput` from each member definition in the group
/// and merges them together. The binding graph is retrieved from the module-level
/// `binding_graph` query.
///
/// # Arguments
///
/// * `db` - The query database
/// * `group_id` - The binding group ID identifying which group to combine inputs for
///
/// # Returns
///
/// A combined `TypeCheckInput` containing:
/// - `bindings`: The full module binding graph (for computing SCCs)
/// - `def_nodes`: Merged mapping from DefId to root expression NodeId
/// - `file_main_stmts`: Merged FileMain statements from all members
/// - `expr_records`: Merged expression metadata from all members
/// - `pattern_records`: Merged pattern metadata from all members
/// - `lowering_errors`: Accumulated lowering errors from all members
#[query]
pub fn typecheck_group_input(db: &Database, group_id: BindingGroupId) -> TypeCheckInput {
    let members = binding_group_members(db, group_id.clone());

    let mut def_nodes: HashMap<DefId, NodeId> = HashMap::new();
    let mut file_main_stmts: HashMap<DefId, Vec<NodeId>> = HashMap::new();
    let mut expr_records = HashMap::new();
    let mut pattern_records = HashMap::new();
    let mut lowering_errors = Vec::new();

    for def_id in &members {
        let input = typecheck_def_input(db, *def_id);

        // Merge def_nodes (DefId → root expression NodeId)
        def_nodes.extend(input.def_nodes);

        // Merge file_main_stmts (FileMain top-level statements)
        file_main_stmts.extend(input.file_main_stmts);

        // Merge expression records
        expr_records.extend(input.expr_records);

        // Merge pattern records
        pattern_records.extend(input.pattern_records);

        // Accumulate lowering errors
        lowering_errors.extend(input.lowering_errors);
    }

    // Get the full binding graph for the module
    let bindings = binding_graph(db, group_id.module);

    TypeCheckInput {
        bindings,
        def_nodes,
        file_main_stmts,
        expr_records,
        pattern_records,
        lowering_errors,
    }
}

/// Typechecks a binding group and returns the type schemes and expression types.
///
/// This query:
/// 1. Retrieves the combined `TypeCheckInput` for the group via `typecheck_group_input`
/// 2. Builds a `BindingGroup` struct from the group members
/// 3. Creates an external scheme lookup closure that queries `annotated_scheme` for each def
/// 4. Delegates to `ray_typing::typecheck_group` for the actual type inference
///
/// The external scheme lookup enables cross-group dependencies: when typechecking a group,
/// any reference to a definition in another group will look up its annotated scheme. Since
/// groups are processed in topological order (via query dependencies), the referenced
/// definition's scheme will already be computed.
///
/// # Arguments
///
/// * `db` - The query database
/// * `group_id` - The binding group ID identifying which group to typecheck
///
/// # Returns
///
/// A `TypeCheckResult` containing:
/// - `schemes`: Inferred type schemes for each definition in the group
/// - `node_tys`: Monomorphic types for each expression node
/// - `local_tys`: Types for local bindings (parameters, let-bindings)
/// - `errors`: Any type errors discovered during inference
#[query]
pub fn typecheck_group(db: &Database, group_id: BindingGroupId) -> TypeCheckResult {
    let input = typecheck_group_input(db, group_id.clone());
    let members = binding_group_members(db, group_id.clone());

    // Build BindingGroup struct for the typechecker
    let group = BindingGroup::new(members.clone());

    // External scheme lookup via query.
    // For definitions outside this group, we look up their scheme.
    // This works because queries are processed in topological order.
    let external_schemes = |def_id: DefId| -> Option<TyScheme> {
        // First try annotated scheme (no typecheck computation needed)
        if let Some(scheme) = annotated_scheme(db, def_id) {
            return Some(scheme);
        }
        // Fall back to inferred scheme from typechecking, but ONLY for
        // definitions outside the current group to avoid cycles.
        if members.contains(&def_id) {
            // Definition is in current group - no external scheme available
            return None;
        }
        // This triggers typecheck of the dependency's binding group,
        // which is safe because binding groups are processed in topological order.
        def_scheme(db, DefTarget::Workspace(def_id))
    };

    // Use QueryEnv for TypecheckEnv (pick file from first member)
    let file_id = members.first().map(|d| d.file).unwrap_or(FileId(0));
    let env = QueryEnv::with_group(db, file_id, group_id);

    ray_typing::typecheck_group(&input, &group, external_schemes, &env)
}

/// Returns the inferred type for a local binding (parameter, let-binding, top-level assignment).
///
/// This query is the primary mechanism for cross-SCC local binding type lookup. When a
/// definition references a local binding owned by another definition (e.g., FileMain's
/// top-level assignments), this query retrieves the type from the owner's typecheck result.
///
/// The query system ensures topological ordering: the owner's binding group is typechecked
/// before any dependent group can look up the local's type.
///
/// # Arguments
///
/// * `db` - The query database
/// * `local_id` - The local binding identifier (contains owner DefId and local index)
///
/// # Returns
///
/// The monomorphic type for the local binding, or `None` if not found.
#[query]
pub fn inferred_local_type(db: &Database, local_id: LocalBindingId) -> Option<Ty> {
    let group_id = binding_group_for_def(db, local_id.owner);
    let result = typecheck_group(db, group_id);
    result.local_tys.get(&local_id).cloned()
}

/// Returns the type scheme for a definition (workspace or library).
///
/// This query provides a unified interface for looking up type schemes regardless
/// of whether the definition is in the current workspace or a compiled library.
///
/// For workspace definitions, this triggers typechecking of the definition's
/// binding group if not already cached, then extracts the scheme from the result.
///
/// For library definitions, the scheme is looked up directly from the library's
/// precomputed data.
///
/// # Arguments
///
/// * `db` - The query database
/// * `target` - The definition target (workspace DefId or library LibraryDefId)
///
/// # Returns
///
/// The type scheme for the definition, or `None` if not found (e.g., for
/// definitions that don't have type schemes like impls).
#[query]
pub fn def_scheme(db: &Database, target: DefTarget) -> Option<TyScheme> {
    match target {
        DefTarget::Workspace(def_id) => {
            let group_id = binding_group_for_def(db, def_id);
            let result = typecheck_group(db, group_id);
            result.schemes.get(&def_id).cloned()
        }
        DefTarget::Library(lib_def_id) => {
            let lib_data = library_data(db, lib_def_id.module.clone())?;
            lib_data.schemes.get(&lib_def_id).cloned()
        }
        DefTarget::Primitive(_) => None, // Primitives don't have user-defined schemes
    }
}

/// Returns the inferred type for an expression node.
///
/// This query looks up the monomorphic type assigned to an AST node during
/// type inference. The node's owner DefId determines which binding group
/// to typecheck.
///
/// # Arguments
///
/// * `db` - The query database
/// * `node_id` - The AST node identifier (contains owner DefId and local index)
///
/// # Returns
///
/// The monomorphic type for the expression, or `None` if not found.
#[query]
pub fn ty_of(db: &Database, node_id: NodeId) -> Option<Ty> {
    let def_id = node_id.owner;
    let group_id = binding_group_for_def(db, def_id);
    let result = typecheck_group(db, group_id);
    result.node_tys.get(&node_id).cloned()
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::{DefId, DefKind},
        node_id::NodeId,
        pathlib::{FilePath, ItemPath, ModulePath},
        resolution::{DefTarget, Resolution},
        ty::Ty,
    };
    use ray_typing::env::TypecheckEnv;

    use crate::{
        queries::{
            deps::{BindingGroupId, binding_group_for_def, binding_groups},
            libraries::LoadedLibraries,
            resolve::name_resolutions,
            transform::file_ast,
            typecheck::{
                QueryEnv, def_scheme, inferred_local_type, ty_of, typecheck_def_input,
                typecheck_group, typecheck_group_input,
            },
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn query_env_struct_def_finds_workspace_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());

        let env = QueryEnv::new(&db, file_id);
        let path = ItemPath::new(module_path, vec!["Point".into()]);

        let result = env.struct_def(&path);

        assert!(result.is_some(), "Should find Point struct");
        let struct_ty = result.unwrap();
        assert_eq!(struct_ty.fields.len(), 2);
    }

    #[test]
    fn query_env_trait_def_finds_workspace_trait() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Eq['a] {
    fn eq(self: 'a, other: 'a) -> bool
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let env = QueryEnv::new(&db, file_id);
        let path = ItemPath::new(module_path, vec!["Eq".into()]);

        let result = env.trait_def(&path);

        assert!(result.is_some(), "Should find Eq trait");
        let trait_ty = result.unwrap();
        assert_eq!(trait_ty.fields.len(), 1);
        assert_eq!(trait_ty.fields[0].name, "eq");
    }

    #[test]
    fn query_env_impls_for_trait_finds_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait ToStr['a] {
    fn to_str(self: 'a) -> string
}

struct Point { x: int }

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let env = QueryEnv::new(&db, file_id);
        let trait_path = ItemPath::new(module_path, vec!["ToStr".into()]);

        let result = env.impls_for_trait(&trait_path);

        assert_eq!(result.len(), 1, "Should find 1 impl for ToStr");
    }

    #[test]
    fn query_env_inherent_impls_finds_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int }

impl object Point {
    fn new(x: int): Point => Point { x }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let env = QueryEnv::new(&db, file_id);
        let type_path = ItemPath::new(module_path, vec!["Point".into()]);

        let result = env.inherent_impls(&type_path);

        assert_eq!(result.len(), 1, "Should find 1 inherent impl for Point");
    }

    #[test]
    fn query_env_resolve_builtin_falls_back_to_core() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let env = QueryEnv::new(&db, file_id);

        let result = env.resolve_builtin("list");

        assert_eq!(result.to_string(), "core::list");
    }

    #[test]
    fn query_env_all_traits_collects_workspace_traits() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Eq['a] {
    fn eq(self: 'a, other: 'a) -> bool
}

trait Ord['a] {
    fn cmp(self: 'a, other: 'a) -> int
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let env = QueryEnv::new(&db, file_id);

        let traits = env.all_traits();

        assert_eq!(traits.len(), 2, "Should find both Eq and Ord traits");
    }

    #[test]
    fn typecheck_def_input_lowers_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
fn add(x: int, y: int) -> int => x + y
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the def_id for the function
        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }))
            .expect("Should have a function def");

        let result = typecheck_def_input(&db, func_def.def_id);

        // The result should have lowered the function
        assert!(
            !result.def_nodes.is_empty(),
            "Should have lowered the function"
        );
    }

    #[test]
    fn typecheck_def_input_lowers_file_main() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
let x = 42
let y = x + 1
"#;
        FileSource::new(&db, file_id, source.to_string());

        // FileMain is always at index 0 for any file
        let file_main_def_id = DefId::new(file_id, 0);

        let result = typecheck_def_input(&db, file_main_def_id);

        // The result should have lowered the top-level statements
        assert!(
            !result.file_main_stmts.is_empty(),
            "Should have lowered FileMain statements"
        );
    }

    #[test]
    fn typecheck_def_input_lowers_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the def_id for the struct
        let file_result = file_ast(&db, file_id);
        let struct_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Struct))
            .expect("Should have a struct def");

        let result = typecheck_def_input(&db, struct_def.def_id);

        // Structs lower but don't produce def_nodes (they're type definitions)
        // Just verify no errors occurred during lowering
        assert!(
            result.lowering_errors.is_empty(),
            "Should have no lowering errors"
        );
    }

    #[test]
    fn typecheck_def_input_lowers_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn origin(): Point => Point { x: 0, y: 0 }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the def_id for the method
        let file_result = file_ast(&db, file_id);
        let method_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Method))
            .expect("Should have a method def");

        let result = typecheck_def_input(&db, method_def.def_id);

        // The result should have lowered the method
        assert!(
            !result.def_nodes.is_empty(),
            "Should have lowered the impl method"
        );
    }

    #[test]
    fn typecheck_group_input_combines_multi_member_group() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Two mutually recursive functions WITHOUT type annotations form a
        // multi-member binding group (SCC). The binding graph only includes edges to
        // unannotated definitions, so we use block body syntax with no parameter types.
        let source = r#"
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get binding groups for the module
        let groups_result = binding_groups(&db, module_path.clone());

        // Find the group containing is_even and is_odd (they should be in the same SCC)
        let file_result = file_ast(&db, file_id);
        let is_even_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "is_even")
            .expect("Should have is_even function");
        let is_odd_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "is_odd")
            .expect("Should have is_odd function");

        // Find which group they're in
        let mut target_group_idx = None;
        for (idx, members) in groups_result.members.iter().enumerate() {
            if members.contains(&is_even_def.def_id) {
                target_group_idx = Some(idx);
                // Verify both are in the same group (mutual recursion)
                assert!(
                    members.contains(&is_odd_def.def_id),
                    "is_even and is_odd should be in the same binding group (SCC)"
                );
                break;
            }
        }
        let group_idx = target_group_idx.expect("Should find binding group containing is_even");

        let group_id = BindingGroupId {
            module: module_path,
            index: group_idx as u32,
        };

        // Call typecheck_group_input
        let combined_input = typecheck_group_input(&db, group_id);

        // Verify the combined input has both functions' def_nodes
        assert!(
            combined_input.def_nodes.contains_key(&is_even_def.def_id),
            "Combined input should contain is_even"
        );
        assert!(
            combined_input.def_nodes.contains_key(&is_odd_def.def_id),
            "Combined input should contain is_odd"
        );

        // Verify expression records were merged (should have records from both functions)
        assert!(
            !combined_input.expr_records.is_empty(),
            "Combined input should have merged expr_records"
        );

        // Verify the binding graph is the full module graph (not empty)
        assert!(
            combined_input.bindings.edges.len() >= 2,
            "Binding graph should have at least the two functions"
        );

        // Note: We don't assert on lowering_errors here because they may be generated
        // due to unresolved operator calls (like `==` and `-`) since we're not loading
        // the core library. The key validation is that the inputs from both defs were merged.
    }

    #[test]
    fn typecheck_group_infers_simple_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Simple fully annotated function
        let source = r#"
fn double(x: int) -> int => x
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let double_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "double")
            .expect("Should have double function");

        // Get its binding group
        let group_id = binding_group_for_def(&db, double_def.def_id);

        // Typecheck the group
        let result = typecheck_group(&db, group_id);

        // Should have inferred a scheme for the function
        assert!(
            result.schemes.contains_key(&double_def.def_id),
            "Should have a scheme for the double function"
        );

        // Should have no type errors for this simple function
        assert!(
            result.errors.is_empty(),
            "Simple annotated function should have no type errors, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn typecheck_group_infers_function_with_literal() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function that returns a literal
        let source = r#"
fn answer() -> int => 42
"#;
        FileSource::new(&db, file_id, source.to_string());

        let file_result = file_ast(&db, file_id);
        let answer_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "answer")
            .expect("Should have answer function");

        let group_id = binding_group_for_def(&db, answer_def.def_id);
        let result = typecheck_group(&db, group_id);

        assert!(
            result.schemes.contains_key(&answer_def.def_id),
            "Should have a scheme for the answer function"
        );
        // Note: Integer literals generate Int[int] predicates which require the core::Int
        // trait to be defined. Without the core library, this will produce an unsolved
        // predicate error. The key validation is that the function got a scheme.
    }

    #[test]
    fn typecheck_group_handles_multi_member_scc() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Two mutually recursive functions (unannotated, so they form an SCC)
        let source = r#"
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let file_result = file_ast(&db, file_id);
        let is_even_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "is_even")
            .expect("Should have is_even function");
        let is_odd_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "is_odd")
            .expect("Should have is_odd function");

        // Both should be in the same group
        let group_id = binding_group_for_def(&db, is_even_def.def_id);

        // Typecheck the group
        let result = typecheck_group(&db, group_id);

        // Should have inferred schemes for both functions
        assert!(
            result.schemes.contains_key(&is_even_def.def_id),
            "Should have a scheme for is_even"
        );
        assert!(
            result.schemes.contains_key(&is_odd_def.def_id),
            "Should have a scheme for is_odd"
        );

        // Note: There may be errors due to unresolved operators (==, -) without core library.
        // The key validation is that both functions got schemes.
    }

    #[test]
    fn typecheck_group_cross_group_reference() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Two annotated functions - they will be in separate binding groups.
        // bar calls foo, so bar depends on foo.
        let source = r#"
fn foo(x: int) -> int => x

fn bar(y: int) -> int => foo(y)
"#;
        FileSource::new(&db, file_id, source.to_string());

        let file_result = file_ast(&db, file_id);
        let foo_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "foo")
            .expect("Should have foo function");
        let bar_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "bar")
            .expect("Should have bar function");

        // Get binding groups
        let foo_group = binding_group_for_def(&db, foo_def.def_id);
        let bar_group = binding_group_for_def(&db, bar_def.def_id);

        // They should be in different groups (both fully annotated)
        assert_ne!(
            foo_group.index, bar_group.index,
            "Annotated functions should be in separate binding groups"
        );

        // Typecheck bar's group - it should successfully look up foo's scheme
        let bar_result = typecheck_group(&db, bar_group);

        assert!(
            bar_result.schemes.contains_key(&bar_def.def_id),
            "Should have a scheme for bar"
        );
        // bar calling foo should typecheck correctly
        assert!(
            bar_result.errors.is_empty(),
            "bar calling foo should typecheck without errors, got: {:?}",
            bar_result.errors
        );
    }

    #[test]
    fn typecheck_group_topological_order_enforced_by_queries() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Chain of dependencies: a -> b -> c (all annotated = separate groups)
        let source = r#"
fn a(x: int) -> int => x

fn b(x: int) -> int => a(x)

fn c(x: int) -> int => b(x)
"#;
        FileSource::new(&db, file_id, source.to_string());

        let file_result = file_ast(&db, file_id);
        let c_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "c")
            .expect("Should have c function");

        // Typecheck c's group - the query system should automatically
        // ensure a and b are typechecked first via annotated_scheme lookups
        let c_group = binding_group_for_def(&db, c_def.def_id);
        let result = typecheck_group(&db, c_group);

        assert!(
            result.schemes.contains_key(&c_def.def_id),
            "Should have a scheme for c"
        );
        assert!(
            result.errors.is_empty(),
            "Chain of function calls should typecheck without errors, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn inferred_local_type_returns_function_parameter_type() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with an annotated parameter
        let source = r#"
fn identity(x: int) -> int => x
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "identity")
            .expect("Should have identity function");

        // Get resolutions for this file to find the parameter's LocalBindingId
        let resolutions = name_resolutions(&db, file_id);

        // Find a Local resolution that is owned by this function
        let param_local_id = resolutions
            .values()
            .filter_map(|r| {
                if let Resolution::Local(local_id) = r {
                    if local_id.owner == func_def.def_id {
                        Some(*local_id)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .next()
            .expect("Should have a local binding for the parameter");

        // Query the inferred type
        let local_ty = inferred_local_type(&db, param_local_id);

        assert!(
            local_ty.is_some(),
            "Should have an inferred type for the parameter"
        );
        // The parameter is annotated as `int`, so we expect that type
        assert_eq!(
            local_ty.unwrap(),
            Ty::int(),
            "Parameter should have type int"
        );
    }

    #[test]
    fn inferred_local_type_works_across_sccs() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Two annotated functions in separate SCCs
        // Each has its own parameter whose type should be retrievable
        let source = r#"
fn foo(a: int) -> int => a

fn bar(b: bool) -> bool => b
"#;
        FileSource::new(&db, file_id, source.to_string());

        let file_result = file_ast(&db, file_id);
        let foo_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "foo")
            .expect("Should have foo function");
        let bar_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "bar")
            .expect("Should have bar function");

        // They should be in different groups (both annotated)
        let foo_group = binding_group_for_def(&db, foo_def.def_id);
        let bar_group = binding_group_for_def(&db, bar_def.def_id);
        assert_ne!(
            foo_group.index, bar_group.index,
            "foo and bar should be in different binding groups"
        );

        // Get resolutions to find parameter LocalBindingIds
        let resolutions = name_resolutions(&db, file_id);

        // Find foo's parameter
        let foo_param_id = resolutions
            .values()
            .filter_map(|r| {
                if let Resolution::Local(local_id) = r {
                    if local_id.owner == foo_def.def_id {
                        Some(*local_id)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .next()
            .expect("Should have a local binding for foo's parameter");

        // Find bar's parameter
        let bar_param_id = resolutions
            .values()
            .filter_map(|r| {
                if let Resolution::Local(local_id) = r {
                    if local_id.owner == bar_def.def_id {
                        Some(*local_id)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .next()
            .expect("Should have a local binding for bar's parameter");

        // Query types for both parameters
        let foo_param_ty = inferred_local_type(&db, foo_param_id);
        let bar_param_ty = inferred_local_type(&db, bar_param_id);

        assert!(
            foo_param_ty.is_some(),
            "Should have type for foo's parameter"
        );
        assert!(
            bar_param_ty.is_some(),
            "Should have type for bar's parameter"
        );

        assert_eq!(
            foo_param_ty.unwrap(),
            Ty::int(),
            "foo's parameter should be int"
        );
        assert_eq!(
            bar_param_ty.unwrap(),
            Ty::bool(),
            "bar's parameter should be bool"
        );
    }

    #[test]
    fn inferred_local_type_for_let_binding_in_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function with a let-binding that creates a local
        let source = r#"
fn get_flag() -> bool {
    x = true
    x
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "get_flag")
            .expect("Should have get_flag function");

        // Get resolutions to find x's LocalBindingId
        let resolutions = name_resolutions(&db, file_id);

        // Find a Local resolution owned by get_flag (should be `x`)
        let x_local_id = resolutions
            .values()
            .filter_map(|r| {
                if let Resolution::Local(local_id) = r {
                    if local_id.owner == func_def.def_id {
                        Some(*local_id)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .next()
            .expect("Should have a local binding for x in get_flag");

        // Query the type of x
        let x_ty = inferred_local_type(&db, x_local_id);

        assert!(
            x_ty.is_some(),
            "Should have an inferred type for let-bound x"
        );
        assert_eq!(
            x_ty.unwrap(),
            Ty::bool(),
            "x should have type bool (from the literal true)"
        );
    }

    #[test]
    fn inferred_local_type_for_file_main_assignment() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Top-level assignment that creates a local binding in FileMain
        let source = r#"
x = true
"#;
        FileSource::new(&db, file_id, source.to_string());

        // FileMain has def_id index 0
        let file_main_def_id = DefId::new(file_id, 0);

        // Get resolutions to find x's LocalBindingId
        let resolutions = name_resolutions(&db, file_id);

        // Find a Local resolution owned by FileMain (should be `x`)
        let x_local_id = resolutions
            .values()
            .filter_map(|r| {
                if let Resolution::Local(local_id) = r {
                    if local_id.owner == file_main_def_id {
                        Some(*local_id)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .next()
            .expect("Should have a local binding for x in FileMain");

        // Query the type of x
        let x_ty = inferred_local_type(&db, x_local_id);

        assert!(
            x_ty.is_some(),
            "Should have an inferred type for FileMain's x"
        );
        assert_eq!(
            x_ty.unwrap(),
            Ty::bool(),
            "x should have type bool (from the literal true)"
        );
    }

    #[test]
    fn typecheck_annotated_function_references_file_main_local() {
        // The annotated function `get_flag` is in its own SCC (fully annotated).
        // FileMain (containing `flag = true`) is in a separate SCC (unannotated).
        // When typechecking `get_flag`, it must look up the type of `flag` via
        // `inferred_local_type`, which requires FileMain to be typechecked first.
        // The query system ensures this topological ordering.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Top-level assignment (unannotated, owned by FileMain) and a function that references it.
        // The function must look up `flag`'s type via inferred_local_type.
        let source = r#"
flag = true

fn get_flag() -> bool => flag
"#;
        FileSource::new(&db, file_id, source.to_string());

        let file_result = file_ast(&db, file_id);

        // Find the function def
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "get_flag")
            .expect("Should have get_flag function");

        // FileMain is always at index 0
        let file_main_def_id = DefId::new(file_id, 0);

        // Verify they are in different binding groups
        let func_group = binding_group_for_def(&db, func_def.def_id);
        let file_main_group = binding_group_for_def(&db, file_main_def_id);
        assert_ne!(
            func_group.index, file_main_group.index,
            "get_flag and FileMain should be in different binding groups"
        );

        // Typecheck FileMain's group first
        let file_main_result = typecheck_group(&db, file_main_group);

        // Typecheck the function's group
        let func_result = typecheck_group(&db, func_group);

        // The function should have a scheme
        assert!(
            func_result.schemes.contains_key(&func_def.def_id),
            "Should have a scheme for get_flag"
        );

        // Verify no type errors for the function
        assert!(
            func_result.errors.is_empty(),
            "get_flag should have no type errors, got: {:?}",
            func_result.errors
        );

        // Verify the cross-SCC local binding lookup works:
        // The `flag` reference inside `get_flag`'s body must resolve to a LocalBindingId
        // owned by FileMain (not by get_flag itself). This is the key validation that
        // inferred_local_type is being used for cross-SCC lookup.
        let resolutions = name_resolutions(&db, file_id);

        // Find the reference to `flag` that is owned by FileMain (the definition site)
        let flag_def_local_id = resolutions
            .values()
            .filter_map(|r| {
                if let Resolution::Local(local_id) = r {
                    if local_id.owner == file_main_def_id {
                        Some(*local_id)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .next()
            .expect("Should have a local binding for flag in FileMain");

        // Find all references to `flag` - there should be at least 2:
        // 1. The definition in FileMain (flag = true)
        // 2. The reference in get_flag's body (=> flag)
        let flag_references: Vec<_> = resolutions
            .iter()
            .filter_map(|(node_id, r)| {
                if let Resolution::Local(local_id) = r {
                    if *local_id == flag_def_local_id {
                        Some(*node_id)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        // We should have at least 2 references to the same local binding:
        // one at the definition site and one inside get_flag's body
        assert!(
            flag_references.len() >= 2,
            "Should have at least 2 references to flag (definition and use in get_flag), got {}",
            flag_references.len()
        );

        // The key validation: the reference inside get_flag resolves to a LocalBindingId
        // whose owner is FileMain, NOT get_flag. This proves that when typechecking get_flag,
        // we must call inferred_local_type(flag_def_local_id) to get flag's type from FileMain.
        assert_eq!(
            flag_def_local_id.owner, file_main_def_id,
            "The flag local binding should be owned by FileMain, not get_flag"
        );

        // Verify inferred_local_type returns the correct type for the cross-SCC local
        let flag_ty = inferred_local_type(&db, flag_def_local_id);
        assert!(
            flag_ty.is_some(),
            "inferred_local_type should return a type for flag"
        );
        assert_eq!(flag_ty.unwrap(), Ty::bool(), "flag should have type bool");

        // Verify FileMain was typechecked successfully (no errors)
        assert!(
            file_main_result.errors.is_empty(),
            "FileMain should have no type errors, got: {:?}",
            file_main_result.errors
        );
    }

    // Tests for def_scheme

    #[test]
    fn def_scheme_returns_scheme_for_annotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Simple fully annotated function
        let source = r#"
fn add(x: int, y: int) -> int => x
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let add_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "add")
            .expect("Should have add function");

        // Query def_scheme via DefTarget::Workspace
        let target = DefTarget::Workspace(add_def.def_id);
        let scheme = def_scheme(&db, target);

        assert!(
            scheme.is_some(),
            "Should have a scheme for the add function"
        );

        let scheme = scheme.unwrap();
        // The function type should be (int, int) -> int
        assert!(
            scheme.vars.is_empty(),
            "Simple function should have no type variables"
        );
    }

    #[test]
    fn def_scheme_returns_scheme_for_unannotated_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Unannotated function (inferred return type)
        let source = r#"
fn get_true() => true
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "get_true")
            .expect("Should have get_true function");

        // Query def_scheme via DefTarget::Workspace
        let target = DefTarget::Workspace(func_def.def_id);
        let scheme = def_scheme(&db, target);

        // Even unannotated functions get inferred schemes after typechecking
        assert!(
            scheme.is_some(),
            "Should have an inferred scheme for the unannotated function"
        );
    }

    #[test]
    fn def_scheme_returns_scheme_for_generic_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Generic function with type parameter
        let source = r#"
fn identity['a](x: 'a) -> 'a => x
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "identity")
            .expect("Should have identity function");

        // Query def_scheme via DefTarget::Workspace
        let target = DefTarget::Workspace(func_def.def_id);
        let scheme = def_scheme(&db, target);

        assert!(
            scheme.is_some(),
            "Should have a scheme for the generic function"
        );

        let scheme = scheme.unwrap();
        // The function should have one type variable ('a)
        assert_eq!(
            scheme.vars.len(),
            1,
            "Generic function should have one type variable"
        );
    }

    #[test]
    fn def_scheme_returns_none_for_impl() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Struct with impl block
        let source = r#"
struct Point { x: int, y: int }

impl Point {
    fn new(x: int, y: int) -> Point => Point { x, y }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the impl's def (not the method, but the impl block itself)
        let file_result = file_ast(&db, file_id);
        let impl_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Impl))
            .expect("Should have an impl def");

        // Query def_scheme via DefTarget::Workspace
        let target = DefTarget::Workspace(impl_def.def_id);
        let scheme = def_scheme(&db, target);

        // Impl blocks don't have type schemes (only their methods do)
        assert!(scheme.is_none(), "Impl block should not have a type scheme");
    }

    #[test]
    fn def_scheme_returns_scheme_for_impl_method() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Struct with impl block containing a method (using `impl object` syntax)
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn origin(): Point => Point { x: 0, y: 0 }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the method's def
        let file_result = file_ast(&db, file_id);
        let method_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Method))
            .expect("Should have a method def");

        // Query def_scheme via DefTarget::Workspace
        let target = DefTarget::Workspace(method_def.def_id);
        let scheme = def_scheme(&db, target);

        assert!(scheme.is_some(), "Method should have a type scheme");
    }

    #[test]
    fn ty_of_returns_type_for_function_body() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Simple function returning a parameter
        let source = r#"
fn identity(x: int) -> int => x
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "identity")
            .expect("Should have identity function");

        // Get the typecheck input to find the definition's root NodeId
        let group_id = binding_group_for_def(&db, func_def.def_id);
        let input = typecheck_group_input(&db, group_id.clone());

        // Get the root expression NodeId for the definition.
        // For functions, this is the entire function definition node (not just the body),
        // which contains ExprKind::Function { params, body }.
        let def_node_id = input
            .def_nodes
            .get(&func_def.def_id)
            .expect("Function should have a definition node");

        // Query ty_of for the definition's root expression
        let def_ty = ty_of(&db, *def_node_id);

        assert!(
            def_ty.is_some(),
            "Should have a type for the function definition expression"
        );
        // The definition root node has the function type (int -> int)
        let ty = def_ty.unwrap();
        assert!(
            matches!(ty, Ty::Func(_, _)),
            "Function definition should have a function type, got {:?}",
            ty
        );
    }

    #[test]
    fn ty_of_returns_type_for_expression_in_expr_records() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Function returning a boolean literal
        let source = r#"
fn get_true() -> bool => true
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "get_true")
            .expect("Should have get_true function");

        // Typecheck the group
        let group_id = binding_group_for_def(&db, func_def.def_id);
        let result = typecheck_group(&db, group_id.clone());

        // The result should have node_tys for expressions
        assert!(
            !result.node_tys.is_empty(),
            "Should have types for expressions in the function"
        );

        // Verify at least one expression has type bool (the `true` literal)
        let has_bool_expr = result.node_tys.values().any(|ty| *ty == Ty::bool());
        assert!(
            has_bool_expr,
            "Should have at least one expression with type bool (the true literal)"
        );

        // Pick any NodeId from node_tys and verify ty_of returns the same value
        let (some_node_id, expected_ty) = result.node_tys.iter().next().unwrap();
        let queried_ty = ty_of(&db, *some_node_id);
        assert_eq!(
            queried_ty.as_ref(),
            Some(expected_ty),
            "ty_of should return the same type as in node_tys"
        );
    }

    #[test]
    fn ty_of_returns_type_for_file_main_statement() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Top-level assignment
        let source = r#"
x = true
"#;
        FileSource::new(&db, file_id, source.to_string());

        // FileMain is always at index 0
        let file_main_def_id = DefId::new(file_id, 0);

        // Typecheck the group
        let group_id = binding_group_for_def(&db, file_main_def_id);
        let result = typecheck_group(&db, group_id);

        // The result should have node_tys for expressions in FileMain
        assert!(
            !result.node_tys.is_empty(),
            "Should have types for expressions in FileMain"
        );

        // Verify at least one expression has type bool (the `true` literal on the RHS)
        let has_bool_expr = result.node_tys.values().any(|ty| *ty == Ty::bool());
        assert!(
            has_bool_expr,
            "Should have at least one expression with type bool (the true literal)"
        );

        // Pick a NodeId from node_tys and verify ty_of returns the same value
        let (some_node_id, expected_ty) = result.node_tys.iter().next().unwrap();
        let queried_ty = ty_of(&db, *some_node_id);
        assert_eq!(
            queried_ty.as_ref(),
            Some(expected_ty),
            "ty_of should return the same type as in node_tys"
        );
    }

    #[test]
    fn ty_of_returns_none_for_invalid_node_id() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Simple function
        let source = r#"
fn foo() -> bool => true
"#;
        FileSource::new(&db, file_id, source.to_string());

        // Get the function's def
        let file_result = file_ast(&db, file_id);
        let func_def = file_result
            .defs
            .iter()
            .find(|d| matches!(d.kind, DefKind::Function { .. }) && d.name == "foo")
            .expect("Should have foo function");

        // Create a NodeId with the correct owner but an invalid index
        let invalid_node_id = NodeId {
            owner: func_def.def_id,
            index: 9999, // Unlikely to be a valid index
        };

        // Query ty_of with the invalid NodeId
        let ty = ty_of(&db, invalid_node_id);

        // Should return None for a non-existent node
        assert!(ty.is_none(), "Should return None for an invalid NodeId");
    }
}
