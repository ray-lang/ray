use ray_query_macros::query;
use ray_shared::{resolution::DefTarget, ty::Ty};

use crate::{
    queries::defs::{def_for_path, impl_def, impls_for_type},
    query::{Database, Query},
};

// ============================================================================
// methods_for_type query
// ============================================================================

#[query]
pub fn methods_for_type(db: &Database, ty: Ty) -> Vec<(String, DefTarget)> {
    // Unwrap reference types to get the inner nominal type (auto-deref for `.` access).
    // RawPtr is NOT unwrapped — no auto-deref for raw pointers.
    let item_path = match &ty {
        Ty::Ref(inner) | Ty::MutRef(inner) => inner.item_path(),
        _ => ty.item_path(),
    };

    let Some(item_path) = item_path else {
        return vec![];
    };

    let Some(type_target) = def_for_path(db, item_path.clone()) else {
        return vec![];
    };

    let impls = impls_for_type(db, type_target);
    let mut methods = Vec::new();

    for impl_target in impls.inherent.iter().chain(impls.trait_impls.iter()) {
        let Some(ref impl_definition) = *impl_def(db, impl_target.clone()) else {
            continue;
        };

        for method in &impl_definition.methods {
            if method.is_static {
                continue;
            }

            methods.push((method.name.clone(), method.target.clone()));
        }
    }

    methods
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        pathlib::{FilePath, ItemPath, ModulePath},
        ty::Ty,
    };

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            methods::methods_for_type,
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn methods_for_type_returns_inherent_instance_methods() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    static fn create(x: int, y: int) -> Point => Point { x, y }
    fn distance(self) -> int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        let ty = Ty::Const(ItemPath::new(module_path, vec!["Point".into()]));
        let methods = methods_for_type(&db, ty);

        // Only instance method "distance" should be returned, not static "create"
        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].0, "distance");
    }

    #[test]
    fn methods_for_type_returns_trait_instance_methods() {
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

struct Point { x: int, y: int }

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        let ty = Ty::Const(ItemPath::new(module_path, vec!["Point".into()]));
        let methods = methods_for_type(&db, ty);

        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].0, "to_str");
    }

    #[test]
    fn methods_for_type_returns_both_inherent_and_trait() {
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

struct Point { x: int, y: int }

impl object Point {
    fn distance(self) -> int => self.x + self.y
}

impl ToStr[Point] {
    fn to_str(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        let ty = Ty::Const(ItemPath::new(module_path, vec!["Point".into()]));
        let methods = methods_for_type(&db, ty);

        assert_eq!(methods.len(), 2);
        let names: Vec<&str> = methods.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains(&"distance"));
        assert!(names.contains(&"to_str"));
    }

    #[test]
    fn methods_for_type_excludes_static_methods() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    static fn create(x: int, y: int) -> Point => Point { x, y }
    static fn origin() -> Point => Point { x: 0, y: 0 }
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        let ty = Ty::Const(ItemPath::new(module_path, vec!["Point".into()]));
        let methods = methods_for_type(&db, ty);

        // Only static methods — should return empty
        assert!(methods.is_empty());
    }

    #[test]
    fn methods_for_type_unwraps_ref_type() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn distance(self) -> int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        // Pass Ty::Ref wrapping the Point type — should auto-deref
        let inner = Ty::Const(ItemPath::new(module_path, vec!["Point".into()]));
        let ty = Ty::Ref(Box::new(inner));
        let methods = methods_for_type(&db, ty);

        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].0, "distance");
    }

    #[test]
    fn methods_for_type_no_deref_for_rawptr() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn distance(self) -> int => self.x + self.y
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        // Pass Ty::RawPtr wrapping the Point type — should NOT auto-deref
        let inner = Ty::Const(ItemPath::new(module_path, vec!["Point".into()]));
        let ty = Ty::RawPtr(Box::new(inner));
        let methods = methods_for_type(&db, ty);

        assert!(methods.is_empty());
    }

    #[test]
    fn methods_for_type_empty_for_no_impls() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        FileSource::new(&db, file_id, "struct Point { x: int }".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        let ty = Ty::Const(ItemPath::new(module_path, vec!["Point".into()]));
        let methods = methods_for_type(&db, ty);

        assert!(methods.is_empty());
    }

    #[test]
    fn methods_for_type_empty_for_non_nominal_type() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Never, Any, and Func types have no item_path — should return empty
        assert!(methods_for_type(&db, Ty::Never).is_empty());
        assert!(methods_for_type(&db, Ty::Any).is_empty());
        assert!(methods_for_type(&db, Ty::Func(vec![Ty::Any], Box::new(Ty::Any))).is_empty());
    }

    #[test]
    fn methods_for_type_empty_for_unknown_type() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // A Ty::Const with a nonexistent path — def_for_path will return None
        let ty = Ty::Const(ItemPath::new(
            ModulePath::from("nonexistent"),
            vec!["Bogus".into()],
        ));
        let methods = methods_for_type(&db, ty);

        assert!(methods.is_empty());
    }

    #[test]
    fn methods_for_type_cross_module_impl() {
        // Struct in module_a, trait + impl in module_b — methods should still be found.
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
        FileMetadata::new(
            &db,
            file_a,
            FilePath::from("module_a/mod.ray"),
            module_a.clone(),
        );

        let source_b = r#"
import module_a with Point

trait Stringify['a] {
    fn stringify(self: 'a) -> string
}

impl Stringify[Point] {
    fn stringify(self: Point) -> string => "Point"
}
"#;
        FileSource::new(&db, file_b, source_b.to_string());
        FileMetadata::new(
            &db,
            file_b,
            FilePath::from("module_b/mod.ray"),
            module_b.clone(),
        );

        let ty = Ty::Const(ItemPath::new(module_a, vec!["Point".into()]));
        let methods = methods_for_type(&db, ty);

        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].0, "stringify");
    }

    #[test]
    fn methods_for_type_primitive_with_impl() {
        // A workspace impl for a primitive type (int) — methods should be found.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
impl object int {
    fn is_positive(self) -> bool => self > 0
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymodule/mod.ray"),
            module_path.clone(),
        );

        let ty = Ty::Const(ItemPath::new(ModulePath::root(), vec!["int".into()]));
        let methods = methods_for_type(&db, ty);

        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].0, "is_positive");
    }

    #[test]
    fn methods_for_type_with_import() {
        // Struct imported into another module — methods found via the original type path.
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_types = ModulePath::from("types");
        let file_types = workspace.add_file(FilePath::from("types/mod.ray"), module_types.clone());
        let module_main = ModulePath::from("main");
        let file_main = workspace.add_file(FilePath::from("main/mod.ray"), module_main.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source_types = r#"
struct Vec2 { x: int, y: int }

impl object Vec2 {
    fn length(self) -> int => self.x + self.y
}
"#;
        FileSource::new(&db, file_types, source_types.to_string());
        FileMetadata::new(
            &db,
            file_types,
            FilePath::from("types/mod.ray"),
            module_types.clone(),
        );

        let source_main = r#"
import types with Vec2
"#;
        FileSource::new(&db, file_main, source_main.to_string());
        FileMetadata::new(
            &db,
            file_main,
            FilePath::from("main/mod.ray"),
            module_main.clone(),
        );

        // Query using the canonical type path (types::Vec2)
        let ty = Ty::Const(ItemPath::new(module_types, vec!["Vec2".into()]));
        let methods = methods_for_type(&db, ty);

        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].0, "length");
    }
}
