//! Export extraction and module index queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::ast::{Decl, Expr, Pattern};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind},
    file_id::FileId,
    local_binding::LocalBindingId,
    pathlib::ModulePath,
};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{parse::parse_file, workspace::WorkspaceSnapshot},
    query::{Database, Query},
};

/// An exported item from a file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExportedItem {
    /// A top-level definition (function, struct, trait, type alias).
    Def(DefId),
    /// A top-level binding (owned by FileMain).
    Local(LocalBindingId),
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
    let parse_result = parse_file(db, file_id);
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
        // Skip FileMain itself - it's not an export
        if matches!(def.kind, DefKind::FileMain) {
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
            | DefKind::StructField => {
                // FileMain, Method, Impl are handled above
                // Primitive is for built-in types, not workspace definitions
                // StructField is nested within struct, not a top-level export
                unreachable!()
            }
        }
    }

    exports
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

    for file_id in file_ids {
        let exports = file_exports(db, file_id);
        merge_exports(&mut index, exports);
    }

    index
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
    use ray_shared::pathlib::{FilePath, ModulePath, Path};

    use crate::{
        queries::{
            exports::{ExportedItem, file_exports, module_def_index},
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    #[test]
    fn file_exports_returns_empty_for_empty_file() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "".to_string());

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
        FileSource::new(&db, file_id, "fn foo() {}\nstruct Bar {}".to_string());

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
        FileSource::new(&db, file1, "fn foo() {}".to_string());
        FileSource::new(&db, file2, "fn bar() {}".to_string());

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
        // Both files define "helper"
        FileSource::new(&db, file1, "fn helper() {}".to_string());
        FileSource::new(&db, file2, "fn helper() {}".to_string());

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
        // All three files define "x"
        FileSource::new(&db, file1, "x = 1".to_string());
        FileSource::new(&db, file2, "x = 2".to_string());
        FileSource::new(&db, file3, "x = 3".to_string());

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
        // file1 has foo and helper, file2 has bar and helper (collision on helper)
        FileSource::new(&db, file1, "fn foo() {}\nfn helper() {}".to_string());
        FileSource::new(&db, file2, "fn bar() {}\nfn helper() {}".to_string());

        let index = module_def_index(&db, ModulePath::from(module_path));

        assert_eq!(index.len(), 3);
        assert!(index.get("foo").unwrap().is_ok());
        assert!(index.get("bar").unwrap().is_ok());
        assert!(index.get("helper").unwrap().is_err());
    }
}
