//! TypecheckEnv implementation for the incremental query system.
//!
//! This module provides `QueryEnv`, which implements the `TypecheckEnv` trait
//! from ray-typing by delegating to the various definition lookup queries.
//! This bridges the gap between the typechecker core (which knows nothing about
//! the query system) and the incremental frontend (which uses queries for
//! definition lookups).

use ray_shared::{
    def::DefId,
    file_id::FileId,
    pathlib::{ItemPath, ModulePath},
    resolution::DefTarget,
    span::Source,
    ty::Ty,
};
use ray_typing::{
    env::TypecheckEnv,
    types::{
        FieldKind, ImplField, ImplKind, ImplTy, NominalKind, StructTy, TraitField, TraitTy, TyScheme,
    },
};

use crate::{
    queries::{
        defs::{
            ImplDef, StructDef, TraitDef, def_for_path, impl_def, impls_for_trait, impls_for_type,
            struct_def, trait_def, traits_in_module,
        },
        libraries::{LoadedLibraries, library_data},
        operators::{lookup_infix_op, lookup_prefix_op},
        parse,
        resolve::resolve_builtin,
        types::annotated_scheme,
        workspace::WorkspaceSnapshot,
    },
    query::Database,
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

    /// Build a Path for a workspace definition by looking up the module path and appending the name.
    fn build_workspace_path(&self, def_id: DefId, name: &str) -> ItemPath {
        let workspace = self.db.get_input::<WorkspaceSnapshot>(());
        if let Some(file_info) = workspace.file_info(def_id.file) {
            ItemPath::new(file_info.module_path.clone(), vec![name.into()])
        } else {
            ItemPath::new(ModulePath::root(), vec![name.into()])
        }
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

/// Helper to convert a DefTarget to an ItemPath.
///
/// For methods (defs with a parent), this builds a fully qualified path like
/// `module::TypeName::method_name` by looking up the parent def.
fn def_target_to_item_path(db: &Database, target: &DefTarget) -> Option<ItemPath> {
    match target {
        DefTarget::Workspace(def_id) => {
            let workspace = db.get_input::<WorkspaceSnapshot>(());
            let parse_result = parse::parse_file(db, def_id.file);

            // Find the def header
            let def_header = parse_result.defs.iter().find(|h| h.def_id == *def_id)?;

            // Get the module path
            let module_path = workspace
                .file_info(def_id.file)
                .map(|info| info.module_path.clone())
                .unwrap_or_else(ModulePath::root);

            // Check if this def has a parent (i.e., it's a method in an impl/trait)
            if let Some(parent_def_id) = def_header.parent {
                // Look up the parent def to get its name (the type or trait name)
                let parent_header = parse_result
                    .defs
                    .iter()
                    .find(|h| h.def_id == parent_def_id)?;

                // Build fully qualified path: module::ParentName::method_name
                Some(ItemPath::new(
                    module_path,
                    vec![parent_header.name.clone(), def_header.name.clone()],
                ))
            } else {
                // Top-level def: module::name
                Some(ItemPath::new(module_path, vec![def_header.name.clone()]))
            }
        }
        DefTarget::Library(lib_def_id) => {
            if let Some(lib_data) = library_data(db, lib_def_id.module.clone()) {
                for (item_path, def) in &lib_data.names {
                    if def == lib_def_id {
                        return Some(item_path.clone());
                    }
                }
            }
            None
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
                // Convert DefTarget back to ItemPath
                match def_target_to_item_path(self.db, &target) {
                    Some(path) => path,
                    None => ItemPath::from(format!("core::{}", name).as_str()),
                }
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
        let trait_path = def_target_to_item_path(self.db, &entry.trait_def)?;
        let method_path = def_target_to_item_path(self.db, &entry.method_def)?;

        Some((trait_path, method_path))
    }

    fn prefix_op(&self, symbol: &str) -> Option<(ItemPath, ItemPath)> {
        let entry = lookup_prefix_op(self.db, symbol.to_string())?;

        let trait_path = def_target_to_item_path(self.db, &entry.trait_def)?;
        let method_path = def_target_to_item_path(self.db, &entry.method_def)?;

        Some((trait_path, method_path))
    }
}

#[cfg(test)]
mod tests {
    use ray_shared::pathlib::{FilePath, ItemPath, ModulePath};
    use ray_typing::env::TypecheckEnv;

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            typecheck::QueryEnv,
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
}
