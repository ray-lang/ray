use ray_query_macros::query;
use ray_shared::resolution::DefTarget;

use crate::{
    queries::defs::{impl_def, impls_for_type},
    query::{Database, Query},
};

// ============================================================================
// associated_items query
// ============================================================================

#[query]
pub fn associated_items(db: &Database, target: DefTarget) -> Vec<(String, DefTarget)> {
    let impls = impls_for_type(db, target);
    let mut items = Vec::new();

    for impl_target in impls.inherent.iter().chain(impls.trait_impls.iter()) {
        let Some(ref impl_definition) = *impl_def(db, impl_target.clone()) else {
            continue;
        };

        for method in &impl_definition.methods {
            if !method.is_static {
                continue;
            }

            items.push((method.name.clone(), method.target.clone()));
        }
    }

    items
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::{DefKind, LibraryDefId},
        file_id::FileId,
        pathlib::{FilePath, ItemPath, ModulePath},
        resolution::DefTarget,
        ty::Ty,
    };
    use ray_typing::types::{ReceiverMode, TyScheme};

    use crate::{
        queries::{
            defs::{ImplDef, MethodInfo, StructDef},
            items::associated_items,
            libraries::{LibraryData, LoadedLibraries},
            parse::parse_file,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    /// Find the DefTarget for a struct by name in a parsed file.
    fn find_struct_def_target(db: &Database, file_id: FileId, name: &str) -> DefTarget {
        let parse_result = parse_file(db, file_id);
        let def = parse_result
            .defs
            .iter()
            .find(|h| h.name == name && matches!(h.kind, DefKind::Struct))
            .expect("struct not found");
        DefTarget::Workspace(def.def_id)
    }

    #[test]
    fn associated_items_returns_static_methods() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    static fn create(x: int, y: int): Point => Point { x, y }
    static fn origin(): Point => Point { x: 0, y: 0 }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let target = find_struct_def_target(&db, file_id, "Point");
        let items = associated_items(&db, target);

        assert_eq!(items.len(), 2);
        let names: Vec<&str> = items.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains(&"create"));
        assert!(names.contains(&"origin"));
    }

    #[test]
    fn associated_items_excludes_instance_methods() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn distance(self): int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let target = find_struct_def_target(&db, file_id, "Point");
        let items = associated_items(&db, target);

        assert!(items.is_empty());
    }

    #[test]
    fn associated_items_returns_both_inherent_and_trait_static() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Zeroed['a] {
    static fn zero() -> 'a
}

struct Point { x: int, y: int }

impl object Point {
    static fn origin(): Point => Point { x: 0, y: 0 }
}

impl Zeroed[Point] {
    static fn zero() -> Point => Point { x: 0, y: 0 }
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let target = find_struct_def_target(&db, file_id, "Point");
        let items = associated_items(&db, target);

        assert_eq!(items.len(), 2);
        let names: Vec<&str> = items.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains(&"origin"));
        assert!(names.contains(&"zero"));
    }

    #[test]
    fn associated_items_mixed_static_and_instance() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    static fn create(x: int, y: int): Point => Point { x, y }
    fn distance(self): int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let target = find_struct_def_target(&db, file_id, "Point");
        let items = associated_items(&db, target);

        // Only static method "create" should be returned, not instance method "distance"
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0, "create");
    }

    #[test]
    fn associated_items_empty_for_no_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());

        let target = find_struct_def_target(&db, file_id, "Point");
        let items = associated_items(&db, target);

        assert!(items.is_empty());
    }

    #[test]
    fn associated_items_empty_for_non_type_target() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = "fn helper(): int => 42";
        FileSource::new(&db, file_id, source.to_string());

        // Find the function def (not a struct)
        let parse_result = parse_file(&db, file_id);
        let func_def = parse_result
            .defs
            .iter()
            .find(|h| h.name == "helper")
            .expect("function not found");
        let target = DefTarget::Workspace(func_def.def_id);

        let items = associated_items(&db, target);

        assert!(items.is_empty());
    }

    #[test]
    fn associated_items_empty_for_primitive() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Primitive with no impls in workspace
        let target = DefTarget::Primitive(ItemPath::new(ModulePath::root(), vec!["int".into()]));
        let items = associated_items(&db, target);

        assert!(items.is_empty());
    }

    #[test]
    fn associated_items_cross_module() {
        // Struct in module_a, trait + static impl in module_b — items should still be found.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_a = ModulePath::from("module_a");
        let file_a = workspace.add_file(FilePath::from("module_a/mod.ray"), module_a.clone());
        let module_b = ModulePath::from("module_b");
        let file_b = workspace.add_file(FilePath::from("module_b/mod.ray"), module_b.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source_a = r#"
struct Point { x: int, y: int }
"#;
        FileSource::new(&db, file_a, source_a.to_string());

        let source_b = r#"
import module_a with Point

trait Zeroed['a] {
    static fn zero() -> 'a
}

impl Zeroed[Point] {
    static fn zero() -> Point => Point { x: 0, y: 0 }
}
"#;
        FileSource::new(&db, file_b, source_b.to_string());

        let target = find_struct_def_target(&db, file_a, "Point");
        let items = associated_items(&db, target);

        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0, "zero");
    }

    #[test]
    fn associated_items_from_library_impl() {
        // Library struct with a library impl containing a static method.
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::collections"));

        // Create the library struct
        let list_def_id = LibraryDefId {
            module: ModulePath::from("core::collections"),
            index: 0,
        };
        let list_path = ItemPath::new(ModulePath::from("core::collections"), vec!["List".into()]);

        core_lib
            .names
            .insert(list_path.clone(), list_def_id.clone());
        core_lib.structs.insert(
            list_def_id.clone(),
            StructDef {
                target: DefTarget::Library(list_def_id.clone()),
                path: list_path.clone(),
                ty: TyScheme::from_mono(Ty::Const(list_path.clone())),
                fields: vec![],
            },
        );

        // Create a library impl with a static method
        let impl_def_id = LibraryDefId {
            module: ModulePath::from("core::collections"),
            index: 1,
        };
        let method_def_id = LibraryDefId {
            module: ModulePath::from("core::collections"),
            index: 2,
        };
        let method_path = ItemPath::new(
            ModulePath::from("core::collections"),
            vec!["List".into(), "empty".into()],
        );

        core_lib.impls.insert(
            impl_def_id.clone(),
            ImplDef {
                target: DefTarget::Library(impl_def_id.clone()),
                type_params: vec![],
                implementing_type: Ty::Const(list_path.clone()),
                trait_ty: None,
                predicates: vec![],
                methods: vec![MethodInfo {
                    target: DefTarget::Library(method_def_id),
                    path: method_path,
                    name: "empty".to_string(),
                    is_static: true,
                    recv_mode: ReceiverMode::None,
                    scheme: TyScheme::from_mono(Ty::Const(list_path.clone())),
                }],
            },
        );

        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        let target = DefTarget::Library(list_def_id);
        let items = associated_items(&db, target);

        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0, "empty");
    }

    #[test]
    fn associated_items_primitive_with_workspace_impl() {
        // Workspace impl adding a static method to a primitive type (int).
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
impl object int {
    static fn from_str(s: string): int => 0
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let target = DefTarget::Primitive(ItemPath::new(ModulePath::root(), vec!["int".into()]));
        let items = associated_items(&db, target);

        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0, "from_str");
    }

    #[test]
    fn associated_items_library_with_workspace_trait_impl() {
        // Library type with a workspace trait impl containing a static method.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up library with a struct
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::option"));

        let option_def_id = LibraryDefId {
            module: ModulePath::from("core::option"),
            index: 0,
        };
        let option_path = ItemPath::new(ModulePath::from("core::option"), vec!["Option".into()]);

        core_lib
            .names
            .insert(option_path.clone(), option_def_id.clone());
        core_lib.structs.insert(
            option_def_id.clone(),
            StructDef {
                target: DefTarget::Library(option_def_id.clone()),
                path: option_path.clone(),
                ty: TyScheme::from_mono(Ty::Const(option_path.clone())),
                fields: vec![],
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        // Workspace defines a trait with a static method and implements it for the library type
        let source = r#"
import core::option with Option

trait Zeroed['a] {
    static fn zero() -> 'a
}

impl Zeroed[Option] {
    static fn zero() -> Option => Option {}
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let target = DefTarget::Library(option_def_id);
        let items = associated_items(&db, target);

        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0, "zero");
    }
}
