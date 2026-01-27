//! TypecheckEnv implementation for the incremental query system.
//!
//! This module provides `QueryEnv`, which implements the `TypecheckEnv` trait
//! from ray-typing by delegating to the various definition lookup queries.
//! This bridges the gap between the typechecker core (which knows nothing about
//! the query system) and the incremental frontend (which uses queries for
//! definition lookups).

use std::collections::HashMap;

use ray_core::{ast::{Decl, Node}, typing::build_typecheck_input};
use ray_query_macros::query;
use ray_shared::{
    def::DefId,
    file_id::FileId,
    node_id::NodeId,
    pathlib::ItemPath,
    resolution::DefTarget,
    span::Source,
    ty::Ty,
};
use ray_typing::{
    TypeCheckInput,
    binding_groups::BindingGraph,
    env::TypecheckEnv,
    types::{
        FieldKind, ImplField, ImplKind, ImplTy, NominalKind, StructTy, TraitField, TraitTy,
        TyScheme,
    },
};

use crate::{
    queries::{
        defs::{
            ImplDef, StructDef, TraitDef, def_for_path, def_path, impl_def, impls_for_trait,
            impls_for_type, struct_def, trait_def, traits_in_module,
        },
        deps::{BindingGroupId, binding_graph, binding_group_members},
        libraries::LoadedLibraries,
        operators::{lookup_infix_op, lookup_prefix_op},
        resolve::{name_resolutions, resolve_builtin},
        transform::file_ast,
        types::annotated_scheme,
        workspace::WorkspaceSnapshot,
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
pub struct QueryEnv<'db> {
    db: &'db Database,
    file_id: FileId,
}

impl<'db> QueryEnv<'db> {
    /// Create a new QueryEnv for a specific file context.
    ///
    /// The file_id determines what imports are in scope for builtin resolution.
    pub fn new(db: &'db Database, file_id: FileId) -> Self {
        QueryEnv { db, file_id }
    }

    /// Convert a defs::TraitDef to a ray_typing::types::TraitTy.
    fn convert_trait_def(&self, trait_def: &TraitDef) -> TraitTy {
        TraitTy {
            path: trait_def.path.clone(),
            ty: trait_def.ty.clone(),
            super_traits: trait_def.super_traits.clone(),
            fields: trait_def
                .methods
                .iter()
                .map(|m| TraitField {
                    kind: FieldKind::Method,
                    name: m.name.clone(),
                    ty: m.scheme.clone(),
                    is_static: m.is_static,
                    recv_mode: m.recv_mode,
                })
                .collect(),
            default_ty: trait_def.default_ty.clone(),
        }
    }

    /// Convert a defs::ImplDef to a ray_typing::types::ImplTy.
    fn convert_impl_def(&self, impl_def: &ImplDef) -> ImplTy {
        let kind = match &impl_def.trait_ty {
            Some(trait_ty) => ImplKind::Trait {
                base_ty: impl_def.implementing_type.clone(),
                trait_ty: trait_ty.clone(),
                ty_args: impl_def
                    .type_params
                    .iter()
                    .map(|v| Ty::Var(v.clone()))
                    .collect(),
            },
            None => ImplKind::Inherent {
                recv_ty: impl_def.implementing_type.clone(),
            },
        };

        ImplTy {
            kind,
            predicates: vec![],
            fields: impl_def
                .methods
                .iter()
                .map(|m| ImplField {
                    kind: FieldKind::Method,
                    path: m.path.clone(),
                    scheme: Some(m.scheme.clone()),
                    is_static: m.is_static,
                    recv_mode: m.recv_mode,
                    src: Source::default(),
                })
                .collect(),
        }
    }

    /// Convert a defs::StructDef to a ray_typing::types::StructTy.
    fn convert_struct_def(&self, struct_def: &StructDef) -> StructTy {
        StructTy {
            kind: NominalKind::Struct,
            path: struct_def.path.clone(),
            ty: struct_def.ty.clone(),
            fields: struct_def
                .fields
                .iter()
                .map(|f| (f.name.clone(), f.ty.clone()))
                .collect(),
        }
    }
}

impl<'db> TypecheckEnv for QueryEnv<'db> {
    fn struct_def(&self, path: &ItemPath) -> Option<StructTy> {
        // Look up the DefTarget for this path
        let target = def_for_path(self.db, path.clone())?;

        // Get the struct definition and convert to StructTy
        let def = struct_def(self.db, target)?;
        Some(self.convert_struct_def(&def))
    }

    fn trait_def(&self, path: &ItemPath) -> Option<TraitTy> {
        let target = def_for_path(self.db, path.clone())?;
        let trait_definition = trait_def(self.db, target)?;
        Some(self.convert_trait_def(&trait_definition))
    }

    fn all_traits(&self) -> Vec<TraitTy> {
        let mut traits = Vec::new();

        // Collect workspace traits
        let workspace = self.db.get_input::<WorkspaceSnapshot>(());
        for module_path in workspace.all_module_paths() {
            let trait_ids = traits_in_module(self.db, module_path.clone());
            for trait_id in trait_ids {
                if let Some(trait_definition) = trait_def(self.db, DefTarget::Workspace(trait_id)) {
                    traits.push(self.convert_trait_def(&trait_definition));
                }
            }
        }

        // Collect library traits
        let libraries = self.db.get_input::<LoadedLibraries>(());
        for (_lib_path, lib_data) in &libraries.libraries {
            for (_lib_def_id, trait_definition) in &lib_data.traits {
                traits.push(self.convert_trait_def(trait_definition));
            }
        }

        traits
    }

    fn impls_for_trait(&self, trait_path: &ItemPath) -> Vec<ImplTy> {
        let target = match def_for_path(self.db, trait_path.clone()) {
            Some(t) => t,
            None => return vec![],
        };

        let impl_targets = impls_for_trait(self.db, target);

        impl_targets
            .into_iter()
            .filter_map(|impl_target| {
                let impl_definition = impl_def(self.db, impl_target)?;
                Some(self.convert_impl_def(&impl_definition))
            })
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
            .filter_map(|impl_target| {
                let impl_definition = impl_def(self.db, impl_target)?;
                Some(self.convert_impl_def(&impl_definition))
            })
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
            .filter_map(|impl_target| {
                let impl_definition = impl_def(self.db, impl_target)?;
                Some(self.convert_impl_def(&impl_definition))
            })
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

    // FileMain is always at index 0 - it owns top-level statements
    if def_id.index == 0 && !file_result.ast.stmts.is_empty() {
        return build_typecheck_input(
            &[],
            &file_result.ast.stmts,
            &file_result.source_map,
            &env,
            &resolutions,
            BindingGraph::new(),
        );
    }

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

#[cfg(test)]
mod tests {
    use ray_shared::def::{DefId, DefKind};
    use ray_shared::pathlib::{FilePath, ItemPath, ModulePath};
    use ray_typing::env::TypecheckEnv;

    use crate::{
        queries::{
            deps::{binding_groups, BindingGroupId},
            libraries::LoadedLibraries,
            transform::file_ast,
            typecheck::{typecheck_def_input, typecheck_group_input, QueryEnv},
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
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
        assert!(!result.def_nodes.is_empty(), "Should have lowered the function");
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
        assert!(!result.file_main_stmts.is_empty(), "Should have lowered FileMain statements");
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
        assert!(result.lowering_errors.is_empty(), "Should have no lowering errors");
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
        assert!(!result.def_nodes.is_empty(), "Should have lowered the impl method");
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
}
