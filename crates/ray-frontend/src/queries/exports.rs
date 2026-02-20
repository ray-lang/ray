//! Export extraction and module index queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::ast::{Decl, ExportKind, Expr, Pattern};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind},
    file_id::FileId,
    local_binding::LocalBindingId,
    pathlib::ModulePath,
    resolution::DefTarget,
};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        imports::resolve_module_path, libraries::LoadedLibraries, parse::parse_file_raw,
        workspace::WorkspaceSnapshot,
    },
    query::{Database, Query},
};

/// An exported item from a file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExportedItem {
    /// A top-level definition (function, struct, trait, type alias).
    Def(DefId),
    /// A top-level binding (owned by FileMain).
    Local(LocalBindingId),
    /// A re-exported definition from another module (via `export ... with name`).
    ReExport(DefTarget),
    /// A re-exported module as a namespace (via `export modulename`).
    Module(ModulePath),
}

/// Extract all exported items from a file.
///
/// Returns a map from export name to the exported item. This includes:
/// - Functions (not methods)
/// - Structs
/// - Traits
/// - Type aliases
/// - Top-level bindings (assignments like `x = 42`)
///
/// Methods and impls are NOT included - they are accessed through their parent type.
#[query]
pub fn file_exports(db: &Database, file_id: FileId) -> HashMap<String, ExportedItem> {
    let parse_result = parse_file_raw(db, file_id);
    let mut exports = HashMap::new();

    // FileMain is at index 0 - it owns top-level bindings
    let file_main_def_id = DefId::new(file_id, 0);
    let mut binding_index = 0u32;

    // First, extract top-level bindings from FileMain (e.g., `x = 42`)
    // FileMain is the first decl and wraps top-level statements
    if let Some(file_main_decl) = parse_result.ast.decls.first() {
        if let Decl::FileMain(stmts) = &file_main_decl.value {
            for stmt in stmts {
                if let Expr::Assign(assign) = &stmt.value {
                    // Extract the name from the LHS pattern
                    if let Pattern::Name(name) = &assign.lhs.value {
                        let binding_name = name.path.to_short_name();
                        let local_id = LocalBindingId::new(file_main_def_id, binding_index);
                        exports.insert(binding_name, ExportedItem::Local(local_id));
                        binding_index += 1;
                    }
                }
            }
        }
    }

    // Then, extract definitions from defs
    for def in &parse_result.defs {
        // Skip FileMain and Test - they're not exports
        if matches!(def.kind, DefKind::FileMain | DefKind::Test) {
            continue;
        }

        // Skip methods - they have a parent (impl or trait)
        if def.parent.is_some() {
            continue;
        }

        // Skip impls - they are not named exports
        if matches!(def.kind, DefKind::Impl) {
            continue;
        }

        match def.kind {
            DefKind::Binding { .. } => {
                // Extern binding -> ExportedItem::Local
                let local_id = LocalBindingId::new(file_main_def_id, binding_index);
                exports.insert(def.name.clone(), ExportedItem::Local(local_id));
                binding_index += 1;
            }
            DefKind::Function { .. }
            | DefKind::Struct
            | DefKind::Trait
            | DefKind::TypeAlias
            | DefKind::AssociatedConst { .. } => {
                // Regular definition -> ExportedItem::Def
                exports.insert(def.name.clone(), ExportedItem::Def(def.def_id));
            }
            DefKind::FileMain
            | DefKind::Method
            | DefKind::Impl
            | DefKind::Primitive
            | DefKind::StructField
            | DefKind::Test => {
                // FileMain, Method, Impl are handled above
                // Primitive is for built-in types, not workspace definitions
                // StructField is nested within struct, not a top-level export
                unreachable!()
            }
        }
    }

    exports
}

/// How names from a re-export are made available.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReExportNames {
    /// `export foo` — re-export the entire module as a namespace handle.
    Namespace,
    /// `export foo with bar, baz` — re-export specific names.
    Selective(Vec<String>),
    /// `export foo with *` — re-export all names from the module.
    Glob,
}

/// A resolved re-export from an `export` statement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedReExport {
    /// The resolved module path being re-exported.
    pub module_path: ModulePath,
    /// How names from this module are re-exported.
    pub names: ReExportNames,
}

/// Resolve all `export` statements in a file.
///
/// Each export statement is resolved to a target module path, similar to
/// how imports are resolved. Returns a list of resolved re-exports.
#[query]
pub fn file_reexports(db: &Database, file_id: FileId) -> Vec<ResolvedReExport> {
    let parse_result = parse_file_raw(db, file_id);
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());

    let current_module = workspace
        .file_info(file_id)
        .map(|info| info.module_path.clone());

    let mut reexports = Vec::new();

    for export in &parse_result.ast.exports {
        let Some(path) = export.path() else {
            continue; // Incomplete export — skip
        };
        let export_path = ModulePath::from(path.to_string().as_str());

        let resolved = resolve_module_path(
            &export_path,
            &workspace,
            &libraries,
            current_module.as_ref(),
        );

        let Ok(module_path) = resolved else {
            // Unresolved export path — skip (error will be reported later)
            continue;
        };

        let names = match &export.kind {
            ExportKind::Path(_) => ReExportNames::Namespace,
            ExportKind::Names(_, name_nodes) => {
                let names = name_nodes.iter().map(|n| n.value.to_short_name()).collect();
                ReExportNames::Selective(names)
            }
            ExportKind::Glob(_) => ReExportNames::Glob,
            ExportKind::Incomplete => continue,
        };

        reexports.push(ResolvedReExport { module_path, names });
    }

    reexports
}

/// A name collision error when multiple definitions export the same name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NameCollision {
    /// The name that collides.
    pub name: String,
    /// The definitions that all export this name.
    pub definitions: Vec<ExportedItem>,
}

/// Build an index of all exported names in a module.
///
/// Aggregates exports from all files in the module into a single namespace.
/// Each name maps to either a unique `ExportedItem` or a collision error if
/// multiple files export the same name.
#[query]
pub fn module_def_index(
    db: &Database,
    module_path: ModulePath,
) -> HashMap<String, Result<ExportedItem, NameCollision>> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());

    let file_ids = match workspace.module_info(&module_path) {
        Some(info) => info.files.clone(),
        None => return HashMap::new(),
    };

    let mut index: HashMap<String, Result<ExportedItem, NameCollision>> = HashMap::new();

    for file_id in &file_ids {
        let exports = file_exports(db, *file_id);
        merge_exports(&mut index, exports);
    }

    // Second pass: incorporate re-exports from `export` statements
    let libraries = db.get_input::<LoadedLibraries>(());
    for file_id in &file_ids {
        let reexports = file_reexports(db, *file_id);
        for reexport in reexports {
            match reexport.names {
                ReExportNames::Namespace => {
                    // `export foo` — add the module as a namespace
                    let alias = reexport
                        .module_path
                        .segments()
                        .last()
                        .map(|s| s.to_string())
                        .unwrap_or_default();
                    let item = ExportedItem::Module(reexport.module_path);
                    merge_single_export(&mut index, alias, item);
                }
                ReExportNames::Selective(names) => {
                    // `export foo with bar, baz` — look up specific names from target
                    let target_exports =
                        resolve_target_exports(db, &reexport.module_path, &libraries);
                    for name in names {
                        if let Some(target) = target_exports.get(&name) {
                            let item = ExportedItem::ReExport(target.clone());
                            merge_single_export(&mut index, name, item);
                        }
                    }
                }
                ReExportNames::Glob => {
                    // `export foo with *` — re-export everything from target
                    let target_exports =
                        resolve_target_exports(db, &reexport.module_path, &libraries);
                    for (name, target) in target_exports {
                        let item = ExportedItem::ReExport(target);
                        merge_single_export(&mut index, name, item);
                    }
                }
            }
        }
    }

    index
}

/// Resolve all named exports from a target module path.
///
/// Looks up the module in the workspace first, then falls back to libraries.
fn resolve_target_exports(
    db: &Database,
    target_module: &ModulePath,
    libraries: &LoadedLibraries,
) -> HashMap<String, DefTarget> {
    // Check workspace first
    let target_index = module_def_index(db, target_module.clone());
    let mut result = HashMap::new();
    for (name, item_result) in &target_index {
        if let Ok(item) = item_result {
            match item {
                ExportedItem::Def(def_id) => {
                    result.insert(name.clone(), DefTarget::Workspace(*def_id));
                }
                ExportedItem::ReExport(target) => {
                    result.insert(name.clone(), target.clone());
                }
                ExportedItem::Module(mp) => {
                    result.insert(name.clone(), DefTarget::Module(mp.clone()));
                }
                ExportedItem::Local(_) => {
                    // Local bindings are not re-exportable as DefTargets
                }
            }
        }
    }

    // If workspace had results, use them
    if !result.is_empty() {
        return result;
    }

    // Fall back to library exports
    if let Some(lib_path) = libraries.library_for_module(target_module) {
        if let Some(lib_data) = libraries.get(&lib_path.clone()) {
            let module_prefix = target_module.to_string();
            for (item_path, lib_def_id) in &lib_data.names {
                let path_str = item_path.to_string();
                if path_str.starts_with(&module_prefix) {
                    let suffix = &path_str[module_prefix.len()..];
                    if let Some(name) = suffix.strip_prefix("::") {
                        if !name.contains("::") {
                            result.insert(name.to_string(), DefTarget::Library(lib_def_id.clone()));
                        }
                    }
                }
            }
        }
    }

    result
}

/// Merge a single export into the index, detecting collisions.
fn merge_single_export(
    index: &mut HashMap<String, Result<ExportedItem, NameCollision>>,
    name: String,
    item: ExportedItem,
) {
    match index.get_mut(&name) {
        None => {
            index.insert(name, Ok(item));
        }
        Some(Ok(existing)) => {
            let collision = NameCollision {
                name: name.clone(),
                definitions: vec![existing.clone(), item],
            };
            index.insert(name, Err(collision));
        }
        Some(Err(collision)) => {
            collision.definitions.push(item);
        }
    }
}

/// Merge exports from a file into the module index, detecting collisions.
fn merge_exports(
    index: &mut HashMap<String, Result<ExportedItem, NameCollision>>,
    exports: HashMap<String, ExportedItem>,
) {
    for (name, item) in exports {
        match index.get_mut(&name) {
            None => {
                // First occurrence of this name
                index.insert(name, Ok(item));
            }
            Some(Ok(existing)) => {
                // Collision: same name exported by multiple files
                let collision = NameCollision {
                    name: name.clone(),
                    definitions: vec![existing.clone(), item],
                };
                index.insert(name, Err(collision));
            }
            Some(Err(collision)) => {
                // Already a collision, add this definition to the list
                collision.definitions.push(item);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        pathlib::{FilePath, ModulePath, Path},
        resolution::DefTarget,
    };

    use crate::{
        queries::{
            exports::{
                ExportedItem, ReExportNames, file_exports, file_reexports, module_def_index,
            },
            libraries::LoadedLibraries,
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn file_exports_returns_empty_for_empty_file() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        assert!(exports.is_empty());
    }

    #[test]
    fn file_exports_extracts_function() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn foo() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        assert_eq!(exports.len(), 1);
        assert!(exports.contains_key("foo"));
        assert!(matches!(exports.get("foo"), Some(ExportedItem::Def(_))));
    }

    #[test]
    fn file_exports_extracts_multiple_functions() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn foo() {}\nfn bar() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        assert_eq!(exports.len(), 2);
        assert!(exports.contains_key("foo"));
        assert!(exports.contains_key("bar"));
    }

    #[test]
    fn file_exports_extracts_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "struct Point { x: int, y: int }".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        assert_eq!(exports.len(), 1);
        assert!(exports.contains_key("Point"));
        assert!(matches!(exports.get("Point"), Some(ExportedItem::Def(_))));
    }

    #[test]
    fn file_exports_extracts_trait() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "trait Foo['a] { fn bar(self: 'a) -> int }".to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        // Only the trait is exported, not the method
        assert_eq!(exports.len(), 1);
        assert!(exports.contains_key("Foo"));
    }

    #[test]
    fn file_exports_extracts_extern_binding() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "extern x: int".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        assert_eq!(exports.len(), 1);
        assert!(exports.contains_key("x"));
        assert!(matches!(exports.get("x"), Some(ExportedItem::Local(_))));
    }

    #[test]
    fn file_exports_extracts_top_level_assignment() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "x = 42".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        assert_eq!(exports.len(), 1);
        assert!(exports.contains_key("x"));
        assert!(matches!(exports.get("x"), Some(ExportedItem::Local(_))));
    }

    #[test]
    fn file_exports_does_not_include_impl_methods() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "struct Foo { x: int }\nimpl object Foo { fn bar(self) => self.x }".to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let exports = file_exports(&db, file_id);

        // Only Foo is exported, not the impl or bar method
        assert_eq!(exports.len(), 1);
        assert!(exports.contains_key("Foo"));
        assert!(!exports.contains_key("bar"));
    }

    #[test]
    fn module_def_index_returns_empty_for_unknown_module() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let index = module_def_index(&db, ModulePath::from("unknown"));

        assert!(index.is_empty());
    }

    #[test]
    fn module_def_index_aggregates_single_file() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = Path::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn foo() {}\nstruct Bar {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            ModulePath::from(module_path.clone()),
        );

        let index = module_def_index(&db, ModulePath::from(module_path));

        assert_eq!(index.len(), 2);
        assert!(index.get("foo").unwrap().is_ok());
        assert!(index.get("Bar").unwrap().is_ok());
    }

    #[test]
    fn module_def_index_aggregates_multiple_files() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = Path::from("mymodule");
        let file1 = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        let file2 = workspace.add_file(FilePath::from("mymodule/utils.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file1, "fn foo() {}".to_string());
        FileMetadata::new(
            &db,
            file1,
            FilePath::from("mymodule/mod.ray"),
            ModulePath::from(module_path.clone()),
        );
        FileSource::new(&db, file2, "fn bar() {}".to_string());
        FileMetadata::new(
            &db,
            file2,
            FilePath::from("mymodule/utils.ray"),
            ModulePath::from(module_path.clone()),
        );

        let index = module_def_index(&db, ModulePath::from(module_path));

        assert_eq!(index.len(), 2);
        assert!(index.get("foo").unwrap().is_ok());
        assert!(index.get("bar").unwrap().is_ok());
    }

    #[test]
    fn module_def_index_detects_collision() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = Path::from("mymodule");
        let file1 = workspace.add_file(FilePath::from("mymodule/a.ray"), module_path.clone());
        let file2 = workspace.add_file(FilePath::from("mymodule/b.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        // Both files define "helper"
        FileSource::new(&db, file1, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            file1,
            FilePath::from("mymodule/a.ray"),
            ModulePath::from(module_path.clone()),
        );
        FileSource::new(&db, file2, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            file2,
            FilePath::from("mymodule/b.ray"),
            ModulePath::from(module_path.clone()),
        );

        let index = module_def_index(&db, ModulePath::from(module_path));

        assert_eq!(index.len(), 1);
        let result = index.get("helper").unwrap();
        assert!(result.is_err());
        let collision = result.as_ref().unwrap_err();
        assert_eq!(collision.name, "helper");
        assert_eq!(collision.definitions.len(), 2);
    }

    #[test]
    fn module_def_index_collision_accumulates_multiple_defs() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = Path::from("mymodule");
        let file1 = workspace.add_file(FilePath::from("mymodule/a.ray"), module_path.clone());
        let file2 = workspace.add_file(FilePath::from("mymodule/b.ray"), module_path.clone());
        let file3 = workspace.add_file(FilePath::from("mymodule/c.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        // All three files define "x"
        FileSource::new(&db, file1, "x = 1".to_string());
        FileMetadata::new(
            &db,
            file1,
            FilePath::from("mymodule/a.ray"),
            ModulePath::from(module_path.clone()),
        );
        FileSource::new(&db, file2, "x = 2".to_string());
        FileMetadata::new(
            &db,
            file2,
            FilePath::from("mymodule/b.ray"),
            ModulePath::from(module_path.clone()),
        );
        FileSource::new(&db, file3, "x = 3".to_string());
        FileMetadata::new(
            &db,
            file3,
            FilePath::from("mymodule/c.ray"),
            ModulePath::from(module_path.clone()),
        );

        let index = module_def_index(&db, ModulePath::from(module_path));

        assert_eq!(index.len(), 1);
        let collision = index.get("x").unwrap().as_ref().unwrap_err();
        assert_eq!(collision.definitions.len(), 3);
    }

    #[test]
    fn module_def_index_mixed_collision_and_unique() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = Path::from("mymodule");
        let file1 = workspace.add_file(FilePath::from("mymodule/a.ray"), module_path.clone());
        let file2 = workspace.add_file(FilePath::from("mymodule/b.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        // file1 has foo and helper, file2 has bar and helper (collision on helper)
        FileSource::new(&db, file1, "fn foo() {}\nfn helper() {}".to_string());
        FileMetadata::new(
            &db,
            file1,
            FilePath::from("mymodule/a.ray"),
            ModulePath::from(module_path.clone()),
        );
        FileSource::new(&db, file2, "fn bar() {}\nfn helper() {}".to_string());
        FileMetadata::new(
            &db,
            file2,
            FilePath::from("mymodule/b.ray"),
            ModulePath::from(module_path.clone()),
        );

        let index = module_def_index(&db, ModulePath::from(module_path));

        assert_eq!(index.len(), 3);
        assert!(index.get("foo").unwrap().is_ok());
        assert!(index.get("bar").unwrap().is_ok());
        assert!(index.get("helper").unwrap().is_err());
    }

    // =========================================================================
    // file_reexports tests
    // =========================================================================

    #[test]
    fn file_reexports_returns_empty_for_no_exports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn foo() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

        let reexports = file_reexports(&db, file_id);

        assert!(reexports.is_empty());
    }

    #[test]
    fn file_reexports_resolves_namespace_export() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let file_id = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "export utils".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let reexports = file_reexports(&db, file_id);

        assert_eq!(reexports.len(), 1);
        assert_eq!(reexports[0].module_path.to_string(), "utils");
        assert_eq!(reexports[0].names, ReExportNames::Namespace);
    }

    #[test]
    fn file_reexports_resolves_selective_export() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let file_id = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(
            &db,
            utils_file,
            "fn decode() {}\nfn to_url() {}".to_string(),
        );
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "export utils with decode, to_url".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let reexports = file_reexports(&db, file_id);

        assert_eq!(reexports.len(), 1);
        assert_eq!(reexports[0].module_path.to_string(), "utils");
        assert_eq!(
            reexports[0].names,
            ReExportNames::Selective(vec!["decode".to_string(), "to_url".to_string()])
        );
    }

    #[test]
    fn file_reexports_resolves_glob_export() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let file_id = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "export utils with *".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let reexports = file_reexports(&db, file_id);

        assert_eq!(reexports.len(), 1);
        assert_eq!(reexports[0].module_path.to_string(), "utils");
        assert_eq!(reexports[0].names, ReExportNames::Glob);
    }

    #[test]
    fn file_reexports_resolves_multiple_exports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let helpers_file =
            workspace.add_file(FilePath::from("helpers/mod.ray"), Path::from("helpers"));
        let file_id = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, utils_file, "fn encode() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, helpers_file, "fn assist() {}".to_string());
        FileMetadata::new(
            &db,
            helpers_file,
            FilePath::from("helpers/mod.ray"),
            ModulePath::from("helpers"),
        );
        FileSource::new(
            &db,
            file_id,
            "export utils\nexport helpers with *".to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let reexports = file_reexports(&db, file_id);

        assert_eq!(reexports.len(), 2);
        assert_eq!(reexports[0].module_path.to_string(), "utils");
        assert_eq!(reexports[0].names, ReExportNames::Namespace);
        assert_eq!(reexports[1].module_path.to_string(), "helpers");
        assert_eq!(reexports[1].names, ReExportNames::Glob);
    }

    #[test]
    fn file_reexports_skips_unresolved_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "export nonexistent with *".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let reexports = file_reexports(&db, file_id);

        assert!(reexports.is_empty(), "unresolved export should be skipped");
    }

    // =========================================================================
    // module_def_index re-export tests
    // =========================================================================

    #[test]
    fn module_def_index_namespace_reexport_adds_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let main_file = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, main_file, "export utils".to_string());
        FileMetadata::new(
            &db,
            main_file,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let index = module_def_index(&db, ModulePath::from("main"));

        assert_eq!(index.len(), 1);
        let utils_entry = index.get("utils").unwrap().as_ref().unwrap();
        assert!(
            matches!(utils_entry, ExportedItem::Module(mp) if mp.to_string() == "utils"),
            "expected ExportedItem::Module, got {:?}",
            utils_entry
        );
    }

    #[test]
    fn module_def_index_selective_reexport_pulls_names() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let main_file = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(
            &db,
            utils_file,
            "fn helper() {}\nfn encode() {}".to_string(),
        );
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, main_file, "export utils with helper".to_string());
        FileMetadata::new(
            &db,
            main_file,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let index = module_def_index(&db, ModulePath::from("main"));

        assert_eq!(index.len(), 1);
        let helper_entry = index.get("helper").unwrap().as_ref().unwrap();
        assert!(
            matches!(
                helper_entry,
                ExportedItem::ReExport(DefTarget::Workspace(_))
            ),
            "expected ExportedItem::ReExport(Workspace), got {:?}",
            helper_entry
        );
        // "encode" should NOT be re-exported
        assert!(index.get("encode").is_none());
    }

    #[test]
    fn module_def_index_glob_reexport_pulls_all_names() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let main_file = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(
            &db,
            utils_file,
            "fn helper() {}\nfn encode() {}".to_string(),
        );
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, main_file, "export utils with *".to_string());
        FileMetadata::new(
            &db,
            main_file,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let index = module_def_index(&db, ModulePath::from("main"));

        assert_eq!(index.len(), 2);
        assert!(matches!(
            index.get("helper").unwrap().as_ref().unwrap(),
            ExportedItem::ReExport(DefTarget::Workspace(_))
        ));
        assert!(matches!(
            index.get("encode").unwrap().as_ref().unwrap(),
            ExportedItem::ReExport(DefTarget::Workspace(_))
        ));
    }

    #[test]
    fn module_def_index_reexport_collides_with_local_def() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let main_file = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        // main defines helper locally AND re-exports helper from utils
        FileSource::new(
            &db,
            main_file,
            "fn helper() {}\nexport utils with helper".to_string(),
        );
        FileMetadata::new(
            &db,
            main_file,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let index = module_def_index(&db, ModulePath::from("main"));

        assert_eq!(index.len(), 1);
        let helper_result = index.get("helper").unwrap();
        assert!(helper_result.is_err(), "should be a collision");
        let collision = helper_result.as_ref().unwrap_err();
        assert_eq!(collision.definitions.len(), 2);
    }

    #[test]
    fn module_def_index_local_defs_and_reexports_merge() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        let main_file = workspace.add_file(FilePath::from("main/mod.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, utils_file, "fn encode() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        // main has local foo AND re-exports encode from utils
        FileSource::new(
            &db,
            main_file,
            "fn foo() {}\nexport utils with encode".to_string(),
        );
        FileMetadata::new(
            &db,
            main_file,
            FilePath::from("main/mod.ray"),
            ModulePath::from("main"),
        );

        let index = module_def_index(&db, ModulePath::from("main"));

        assert_eq!(index.len(), 2);
        // Local def
        assert!(matches!(
            index.get("foo").unwrap().as_ref().unwrap(),
            ExportedItem::Def(_)
        ));
        // Re-exported def
        assert!(matches!(
            index.get("encode").unwrap().as_ref().unwrap(),
            ExportedItem::ReExport(DefTarget::Workspace(_))
        ));
    }
}
