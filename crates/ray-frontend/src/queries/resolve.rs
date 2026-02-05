//! Name resolution query for the incremental compiler.

use std::collections::HashMap;

use ray_core::sema::resolve_names_in_file;
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId,
    node_id::NodeId,
    pathlib::ModulePath,
    resolution::{DefTarget, Resolution},
};

use crate::{
    queries::{
        exports::{ExportedItem, file_exports, module_def_index},
        imports::{ImportNames, resolved_imports},
        libraries::LoadedLibraries,
        parse::parse_file,
        workspace::WorkspaceSnapshot,
    },
    query::{Database, Query},
};

/// Resolve all name references in a file.
///
/// Returns a mapping from NodeId to Resolution for every name reference in
/// the file. This includes:
/// - Local bindings (parameters, let-bindings) -> Resolution::Local
/// - Module exports (same module) -> Resolution::Def
/// - Sibling file exports -> Resolution::Def
/// - Imported module exports -> Resolution::Def (both qualified like `io::read` and unqualified)
/// - Library imports -> Resolution::Def with DefTarget::Library
/// - Unresolved names -> not in the map (or Resolution::Error for diagnostics)
#[query]
pub fn name_resolutions(db: &Database, file_id: FileId) -> HashMap<NodeId, Resolution> {
    let parse_result = parse_file(db, file_id);
    let resolved = resolved_imports(db, file_id);
    let libraries = db.get_input::<LoadedLibraries>(());

    // Get the combined unqualified exports (reuse file_scope query)
    // This already includes module exports, sibling exports, and selective imports
    // with correct priority (module > sibling > imports)
    let combined_exports = file_scope(db, file_id);

    // Build imports map: alias -> module_path (for qualified access like `io::read`)
    let mut imports_map: HashMap<String, ModulePath> = HashMap::new();
    for (alias, import_result) in &resolved {
        if let Ok(resolved_import) = import_result {
            if matches!(resolved_import.names, ImportNames::Namespace) {
                // Namespace import: `import utils` enables `utils::foo` (qualified access only)
                imports_map.insert(alias.clone(), resolved_import.module_path.clone());
            }
        }
    }

    // Create closure to look up exports for a module path
    let module_exports = |module_path: &ModulePath| -> Option<HashMap<String, DefTarget>> {
        // Check if this is a library import or workspace import
        if libraries.library_for_module(module_path).is_some() {
            // Library import - get exports from library
            Some(get_library_exports(&libraries, module_path))
        } else {
            // Workspace import
            let imported_module_index = module_def_index(db, module_path.clone());
            Some(convert_to_def_targets(&imported_module_index))
        }
    };

    resolve_names_in_file(
        &parse_result.ast,
        &imports_map,
        &combined_exports,
        module_exports,
    )
}

/// The top-level scope for a file: names that are visible without qualification.
///
/// This includes:
/// - Module exports (same module)
/// - Sibling file exports
/// - Selective imports (`import foo with bar` makes `bar` visible)
/// - Library exports from selective imports
///
/// This is cached as a query so that multiple lookups don't rebuild the scope.
#[query]
pub fn file_scope(db: &Database, file_id: FileId) -> HashMap<String, DefTarget> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());
    let resolved = resolved_imports(db, file_id);

    // Get file info to know which module this file belongs to
    let file_info = match workspace.file_info(file_id) {
        Some(info) => info,
        None => return HashMap::new(),
    };

    // Get exports from the file's module
    let module_index = module_def_index(db, file_info.module_path.clone());
    let mut combined_exports = convert_to_def_targets(&module_index);

    // Add sibling exports
    let sibling_exports = compute_sibling_exports(db, file_id, &file_info.module_path, &workspace);
    for (sibling_name, target) in sibling_exports {
        combined_exports.entry(sibling_name).or_insert(target);
    }

    // Add selective and glob imports
    for (_alias, import_result) in &resolved {
        if let Ok(resolved_import) = import_result {
            let module_path = &resolved_import.module_path;

            let imported_exports = if libraries.library_for_module(&module_path).is_some() {
                get_library_exports(&libraries, module_path)
            } else {
                let imported_module_index = module_def_index(db, module_path.clone());
                convert_to_def_targets(&imported_module_index)
            };

            match &resolved_import.names {
                ImportNames::Selective(names) => {
                    // Bring only the specified names into scope
                    for imported_name in names {
                        if let Some(target) = imported_exports.get(imported_name) {
                            combined_exports
                                .entry(imported_name.clone())
                                .or_insert(target.clone());
                        }
                    }
                }
                ImportNames::Glob => {
                    // Bring all exported names into scope
                    for (name, target) in imported_exports {
                        combined_exports.entry(name).or_insert(target);
                    }
                }
                ImportNames::Namespace => {
                    // Namespace imports don't bring names directly into scope
                }
            }
        }
    }

    combined_exports
}

/// Resolve a builtin name in the context of a file.
///
/// This performs name resolution for a single name, using the same scope
/// that would be visible at the top level of the given file.
///
/// This is NOT hardcoded - it uses the normal name resolution rules.
/// If a user defines their own `list` type and it's in scope, that's what
/// they get. If they're using the standard library and have `list` imported,
/// they get that.
///
/// Returns `None` if the name is not in scope.
#[query]
pub fn resolve_builtin(db: &Database, file_id: FileId, name: String) -> Option<DefTarget> {
    let scope = file_scope(db, file_id);
    scope.get(&name).cloned()
}

/// Convert module_def_index results to DefTarget map.
fn convert_to_def_targets(
    index: &HashMap<String, Result<ExportedItem, crate::queries::exports::NameCollision>>,
) -> HashMap<String, DefTarget> {
    let mut result = HashMap::new();
    for (name, item_result) in index {
        if let Ok(item) = item_result {
            if let Some(target) = exported_item_to_def_target(item) {
                result.insert(name.clone(), target);
            }
        }
    }
    result
}

/// Get exports from a library module.
///
/// Returns a map from exported name to DefTarget::Library.
fn get_library_exports(
    libraries: &LoadedLibraries,
    module_path: &ModulePath,
) -> HashMap<String, DefTarget> {
    let mut result = HashMap::new();

    // Find which library contains this module
    let lib_path = match libraries.library_for_module(&module_path) {
        Some(path) => path.clone(),
        None => return result,
    };

    // Get the library data
    let lib_data = match libraries.get(&lib_path) {
        Some(data) => data,
        None => return result,
    };

    // Collect exports from the library's names index
    // The item paths are full paths like "core::io::read", we need to filter
    // for paths that start with the module_path
    let module_prefix = module_path.to_string();

    for (item_path, lib_def_id) in &lib_data.names {
        let path_str = item_path.to_string();
        // Check if this path belongs to the imported module
        if path_str.starts_with(&module_prefix) {
            // Extract the name: for "core::io::read" with module "core::io", name is "read"
            let suffix = &path_str[module_prefix.len()..];
            if let Some(name) = suffix.strip_prefix("::") {
                // Only direct children (no more :: in the name)
                if !name.contains("::") {
                    result.insert(name.to_string(), DefTarget::Library(lib_def_id.clone()));
                }
            }
        }
    }

    result
}

/// Convert ExportedItem to DefTarget if possible.
fn exported_item_to_def_target(item: &ExportedItem) -> Option<DefTarget> {
    match item {
        ExportedItem::Def(def_id) => Some(DefTarget::Workspace(*def_id)),
        ExportedItem::Local(_) => {
            // Local bindings at module level are not accessible as DefTargets
            // They are accessed differently (through the FileMain)
            None
        }
    }
}

/// Compute exports from sibling files in the same module.
///
/// Sibling exports are definitions from other files in the same module
/// that this file can reference without imports.
fn compute_sibling_exports(
    db: &Database,
    file_id: FileId,
    module_path: &ModulePath,
    workspace: &WorkspaceSnapshot,
) -> HashMap<String, DefTarget> {
    let mut sibling_exports = HashMap::new();

    if let Some(module_info) = workspace.module_info(module_path) {
        for &sibling_id in &module_info.files {
            if sibling_id == file_id {
                // Skip self
                continue;
            }

            let exports = file_exports(db, sibling_id);
            for (name, item) in exports {
                if let Some(target) = exported_item_to_def_target(&item) {
                    sibling_exports.entry(name).or_insert(target);
                }
            }
        }
    }

    sibling_exports
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::LibraryDefId,
        pathlib::{FilePath, ItemPath, ModulePath, Path},
        resolution::{DefTarget, Resolution},
        ty::Ty,
    };
    use ray_typing::types::TyScheme;

    use crate::{
        queries::{
            libraries::{LibraryData, LoadedLibraries},
            resolve::{name_resolutions, resolve_builtin},
            workspace::{CompilerOptions, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    /// Helper to set up CompilerOptions with no_core = true (no implicit imports).
    fn setup_no_core(db: &Database) {
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });
    }

    #[test]
    fn name_resolutions_returns_empty_for_empty_file() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, file_id, "".to_string());

        let resolutions = name_resolutions(&db, file_id);

        assert!(resolutions.is_empty());
    }

    #[test]
    fn name_resolutions_resolves_local_parameter() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        // fn f(x) { x }
        FileSource::new(&db, file_id, "fn f(x) { x }".to_string());

        let resolutions = name_resolutions(&db, file_id);

        // Should have resolutions for the parameter and its usage
        // The exact count depends on how the parser assigns NodeIds
        assert!(!resolutions.is_empty());
        // All resolutions should be Local (parameter reference)
        for (_, res) in &resolutions {
            assert!(matches!(res, Resolution::Local(_)));
        }
    }

    #[test]
    fn name_resolutions_resolves_sibling_export() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = Path::from("mymodule");
        // Two files in the same module
        let file1 = workspace.add_file(FilePath::from("mymodule/a.ray"), module_path.clone());
        let file2 = workspace.add_file(FilePath::from("mymodule/b.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // file1 defines helper
        FileSource::new(&db, file1, "fn helper() {}".to_string());
        // file2 uses helper
        FileSource::new(&db, file2, "fn main() { helper() }".to_string());

        let resolutions = name_resolutions(&db, file2);

        // Should have resolution for helper() call
        // Look for a Def resolution pointing to helper
        let has_def_resolution = resolutions
            .values()
            .any(|res| matches!(res, Resolution::Def(_)));
        assert!(has_def_resolution, "Should resolve sibling export 'helper'");
    }

    #[test]
    fn name_resolutions_resolves_qualified_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with a helper function
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that imports utils and uses qualified access
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        // Use qualified access: utils::helper()
        FileSource::new(
            &db,
            main_file,
            "import utils\nfn main() { utils::helper() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Should have resolution for utils::helper() call
        let has_def_resolution = resolutions
            .values()
            .any(|res| matches!(res, Resolution::Def(_)));
        assert!(
            has_def_resolution,
            "Should resolve qualified import 'utils::helper'"
        );
    }

    #[test]
    fn name_resolutions_selective_import_enables_unqualified_access() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with a helper function
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that selectively imports helper
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        // Selective import: `import utils with helper` enables bare `helper()`
        FileSource::new(
            &db,
            main_file,
            "import utils with helper\nfn main() { helper() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Should have resolution for helper() call from selective import
        let has_def_resolution = resolutions
            .values()
            .any(|res| matches!(res, Resolution::Def(_)));
        assert!(
            has_def_resolution,
            "Selective import should enable unqualified 'helper'"
        );
    }

    #[test]
    fn name_resolutions_local_shadows_export() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = Path::from("mymodule");
        let file1 = workspace.add_file(FilePath::from("mymodule/a.ray"), module_path.clone());
        let file2 = workspace.add_file(FilePath::from("mymodule/b.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // file1 defines x as a function
        FileSource::new(&db, file1, "fn x() {}".to_string());
        // file2 has local x parameter that should shadow the sibling export
        FileSource::new(&db, file2, "fn f(x) { x }".to_string());

        let resolutions = name_resolutions(&db, file2);

        // All resolutions for x should be Local, not Def
        for (_, res) in &resolutions {
            if matches!(res, Resolution::Local(_)) {
                // This is expected - local shadows export
            } else if matches!(res, Resolution::Def(_)) {
                panic!("Local parameter should shadow sibling export");
            }
        }
    }

    #[test]
    fn name_resolutions_handles_let_binding() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        // fn f() { y = 1; y }
        FileSource::new(&db, file_id, "fn f() { y = 1\n y }".to_string());

        let resolutions = name_resolutions(&db, file_id);

        // Should have resolutions for y binding and y usage
        assert!(!resolutions.is_empty());
        // Should all be Local
        for (_, res) in &resolutions {
            assert!(matches!(res, Resolution::Local(_)));
        }
    }

    #[test]
    fn name_resolutions_selective_import_only_brings_named_items() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with two functions
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that selectively imports only `foo`
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // utils has foo and bar
        FileSource::new(&db, utils_file, "fn foo() {}\nfn bar() {}".to_string());
        // main imports only foo, then tries to use both foo and bar unqualified
        FileSource::new(
            &db,
            main_file,
            "import utils with foo\nfn main() { foo()\n bar() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Count Def resolutions - should only have 1 (for foo), not 2 (bar should be unresolved)
        let def_count = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(_)))
            .count();

        // Only foo should resolve, bar should not
        assert_eq!(
            def_count, 1,
            "Selective import should only bring 'foo' into scope, not 'bar'"
        );
    }

    #[test]
    fn name_resolutions_selective_import_does_not_enable_qualified_access() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with a function
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that selectively imports foo
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn foo() {}".to_string());
        // Selective import: `import utils with foo` does NOT enable `utils::foo`
        FileSource::new(
            &db,
            main_file,
            "import utils with foo\nfn main() { utils::foo() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Count Def resolutions - should be 0 (utils::foo should NOT resolve)
        let def_count = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(_)))
            .count();

        assert_eq!(
            def_count, 0,
            "Selective import should NOT enable qualified access 'utils::foo'"
        );
    }

    #[test]
    fn name_resolutions_plain_import_does_not_bring_names_into_scope() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with two functions
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that plain imports utils
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // utils has foo and bar
        FileSource::new(&db, utils_file, "fn foo() {}\nfn bar() {}".to_string());
        // main plain imports utils, then tries to use foo and bar unqualified (should NOT resolve)
        FileSource::new(
            &db,
            main_file,
            "import utils\nfn main() { foo()\n bar() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Count Def resolutions - should be 0 (foo and bar are NOT in scope)
        let def_count = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(_)))
            .count();

        // Neither foo nor bar should resolve unqualified
        assert_eq!(
            def_count, 0,
            "Plain import should NOT bring 'foo' or 'bar' into scope"
        );
    }

    #[test]
    fn name_resolutions_plain_import_allows_qualified_access() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with two functions
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that plain imports utils
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // utils has foo and bar
        FileSource::new(&db, utils_file, "fn foo() {}\nfn bar() {}".to_string());
        // main plain imports utils, then uses qualified access
        FileSource::new(
            &db,
            main_file,
            "import utils\nfn main() { utils::foo()\n utils::bar() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Count Def resolutions - should be 2 (both qualified accesses resolve)
        let def_count = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(_)))
            .count();

        // Both utils::foo and utils::bar should resolve
        assert_eq!(
            def_count, 2,
            "Plain import should allow qualified access to 'utils::foo' and 'utils::bar'"
        );
    }

    #[test]
    fn name_resolutions_glob_import_brings_all_names_into_scope() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with two functions
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that glob imports utils
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // utils has foo and bar
        FileSource::new(&db, utils_file, "fn foo() {}\nfn bar() {}".to_string());
        // main glob imports utils, then uses both foo and bar unqualified
        FileSource::new(
            &db,
            main_file,
            "import utils with *\nfn main() { foo()\n bar() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Count Def resolutions - should be 2 (both foo and bar resolve unqualified)
        let def_count = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(_)))
            .count();

        // Both foo and bar should resolve unqualified
        assert_eq!(
            def_count, 2,
            "Glob import should bring both 'foo' and 'bar' into scope"
        );
    }

    #[test]
    fn name_resolutions_glob_import_does_not_enable_qualified_access() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create utils module with a function
        let utils_file = workspace.add_file(FilePath::from("utils/mod.ray"), Path::from("utils"));
        // Create main module that glob imports utils
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // utils has foo
        FileSource::new(&db, utils_file, "fn foo() {}".to_string());
        // Glob import: `import utils with *` should NOT enable `utils::foo`
        FileSource::new(
            &db,
            main_file,
            "import utils with *\nfn main() { utils::foo() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Count Def resolutions - should be 0 (qualified access should NOT work)
        let def_count = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(_)))
            .count();

        assert_eq!(
            def_count, 0,
            "Glob import should NOT enable qualified access 'utils::foo'"
        );
    }

    #[test]
    fn name_resolutions_resolves_library_import_qualified() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::io module containing a "read" function
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));

        // Create a LibraryDefId for the read function
        let read_def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 0,
        };
        let read_path = ItemPath {
            module: ModulePath::from("core::io"),
            item: vec!["read".to_string()],
        };

        // Add the name -> def_id mapping
        core_lib.names.insert(read_path, read_def_id.clone());

        // Add a scheme for core::io::read
        core_lib.schemes.insert(
            read_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);
        setup_no_core(&db);

        // Import core::io and use qualified access: io::read()
        FileSource::new(
            &db,
            main_file,
            "import core::io\nfn main() { io::read() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Should have a Def resolution for io::read() pointing to a Library target
        let library_resolutions: Vec<_> = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(DefTarget::Library(_))))
            .collect();

        assert_eq!(
            library_resolutions.len(),
            1,
            "Should resolve qualified library import 'io::read' to DefTarget::Library"
        );
    }

    #[test]
    fn name_resolutions_resolves_library_selective_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::io module containing "read" and "write" functions
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));

        // Create LibraryDefIds for read and write
        let read_def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 0,
        };
        let write_def_id = LibraryDefId {
            module: ModulePath::from("core::io"),
            index: 1,
        };
        let read_path = ItemPath {
            module: ModulePath::from("core::io"),
            item: vec!["read".to_string()],
        };
        let write_path = ItemPath {
            module: ModulePath::from("core::io"),
            item: vec!["write".to_string()],
        };

        // Add name -> def_id mappings
        core_lib.names.insert(read_path, read_def_id.clone());
        core_lib.names.insert(write_path, write_def_id.clone());

        // Add schemes
        core_lib.schemes.insert(
            read_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        core_lib.schemes.insert(
            write_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);
        setup_no_core(&db);

        // Selective import: only "read" should be available unqualified
        FileSource::new(
            &db,
            main_file,
            "import core::io with read\nfn main() { read()\n write() }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Count library resolutions - should be 1 (only read), not 2 (write should be unresolved)
        let library_count = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(DefTarget::Library(_))))
            .count();

        assert_eq!(
            library_count, 1,
            "Selective library import should only bring 'read' into scope, not 'write'"
        );
    }

    #[test]
    fn resolve_builtin_finds_workspace_definition() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // Define a struct named "list"
        FileSource::new(&db, file_id, "struct list { items: int }".to_string());

        let result = resolve_builtin(&db, file_id, "list".to_string());
        assert!(
            result.is_some(),
            "Should resolve 'list' to workspace definition"
        );
        assert!(
            matches!(result, Some(DefTarget::Workspace(_))),
            "Should be a workspace target"
        );
    }

    #[test]
    fn resolve_builtin_finds_library_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::collections containing "list"
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::collections"));

        let list_def_id = LibraryDefId {
            module: ModulePath::from("core::collections"),
            index: 0,
        };
        let list_path = ItemPath::new(ModulePath::from("core::collections"), vec!["list".into()]);
        core_lib.names.insert(list_path, list_def_id.clone());
        core_lib.schemes.insert(
            list_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);
        setup_no_core(&db);

        // Selective import: `import core::collections with list`
        FileSource::new(
            &db,
            main_file,
            "import core::collections with list\nfn main() {}".to_string(),
        );

        let result = resolve_builtin(&db, main_file, "list".to_string());
        assert!(
            result.is_some(),
            "Should resolve 'list' from library import"
        );
        assert!(
            matches!(result, Some(DefTarget::Library(_))),
            "Should be a library target"
        );
    }

    #[test]
    fn resolve_builtin_returns_none_for_unimported_name() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let result = resolve_builtin(&db, file_id, "list".to_string());
        assert!(result.is_none(), "Should return None for name not in scope");
    }

    #[test]
    fn resolve_builtin_finds_sibling_export() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        // Two files in the same module
        let file1 = workspace.add_file(FilePath::from("mymodule/a.ray"), module_path.clone());
        let file2 = workspace.add_file(FilePath::from("mymodule/b.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        // file1 defines MyType
        FileSource::new(&db, file1, "struct MyType {}".to_string());
        // file2 can see MyType from sibling
        FileSource::new(&db, file2, "fn use_it(x: MyType) {}".to_string());

        // From file2's perspective, MyType should be resolvable
        let result = resolve_builtin(&db, file2, "MyType".to_string());
        assert!(result.is_some(), "Should resolve sibling export");
        assert!(
            matches!(result, Some(DefTarget::Workspace(_))),
            "Should be a workspace target"
        );
    }

    #[test]
    fn resolve_builtin_workspace_shadows_library() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::collections containing "list"
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::collections"));

        let list_def_id = LibraryDefId {
            module: ModulePath::from("core::collections"),
            index: 0,
        };
        let list_path = ItemPath::new(ModulePath::from("core::collections"), vec!["list".into()]);
        core_lib.names.insert(list_path, list_def_id.clone());
        core_lib.schemes.insert(
            list_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);
        setup_no_core(&db);

        // Workspace defines its own "list", and also imports from library
        FileSource::new(
            &db,
            file_id,
            "import core::collections with list\nstruct list {}".to_string(),
        );

        let result = resolve_builtin(&db, file_id, "list".to_string());
        assert!(result.is_some(), "Should resolve 'list'");
        // Workspace definition should shadow library import
        assert!(
            matches!(result, Some(DefTarget::Workspace(_))),
            "Workspace definition should shadow library import"
        );
    }

    #[test]
    fn name_resolutions_resolves_nested_module_path() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::collections module containing "HashMap"
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::collections"));

        // Create a LibraryDefId for HashMap
        let hashmap_def_id = LibraryDefId {
            module: ModulePath::from("core::collections"),
            index: 0,
        };
        let hashmap_path = ItemPath::new(
            ModulePath::from("core::collections"),
            vec!["HashMap".into()],
        );

        // Add the name -> def_id mapping
        core_lib.names.insert(hashmap_path, hashmap_def_id.clone());

        // Add a scheme for HashMap
        core_lib.schemes.insert(
            hashmap_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);
        setup_no_core(&db);

        // Import core and use nested path: core::collections::HashMap
        // This tests 3-segment path resolution
        FileSource::new(
            &db,
            main_file,
            "import core\nfn main() { core::collections::HashMap }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Should have a Def resolution for core::collections::HashMap
        let library_resolutions: Vec<_> = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(DefTarget::Library(_))))
            .collect();

        assert!(
            !library_resolutions.is_empty(),
            "Should resolve nested module path 'core::collections::HashMap' to DefTarget::Library. Got resolutions: {:?}",
            resolutions
        );
    }

    #[test]
    fn name_resolutions_resolves_deeply_nested_module_path() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with std::collections::hash_map module containing "HashMap"
        let mut libraries = LoadedLibraries::default();
        let mut std_lib = LibraryData::default();
        std_lib.modules.push(ModulePath::from("std::collections"));
        std_lib.modules.push(ModulePath::from("std::collections::hash_map"));

        // Create a LibraryDefId for HashMap in the deeply nested module
        let hashmap_def_id = LibraryDefId {
            module: ModulePath::from("std::collections::hash_map"),
            index: 0,
        };
        let hashmap_path = ItemPath::new(
            ModulePath::from("std::collections::hash_map"),
            vec!["HashMap".into()],
        );

        // Add the name -> def_id mapping
        std_lib.names.insert(hashmap_path, hashmap_def_id.clone());

        // Add a scheme for HashMap
        std_lib.schemes.insert(
            hashmap_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("std"), std_lib);
        db.set_input::<LoadedLibraries>((), libraries);
        setup_no_core(&db);

        // Import std and use deeply nested path: std::collections::hash_map::HashMap
        // This tests 4-segment path resolution
        FileSource::new(
            &db,
            main_file,
            "import std\nfn main() { std::collections::hash_map::HashMap }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Should have a Def resolution for std::collections::hash_map::HashMap
        let library_resolutions: Vec<_> = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(DefTarget::Library(_))))
            .collect();

        assert!(
            !library_resolutions.is_empty(),
            "Should resolve deeply nested path 'std::collections::hash_map::HashMap' to DefTarget::Library. Got resolutions: {:?}",
            resolutions
        );
    }

    #[test]
    fn name_resolutions_resolves_relative_path_from_submodule_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with std::collections::hash_map module containing "HashMap"
        let mut libraries = LoadedLibraries::default();
        let mut std_lib = LibraryData::default();
        std_lib.modules.push(ModulePath::from("std::collections"));
        std_lib.modules.push(ModulePath::from("std::collections::hash_map"));

        // Create a LibraryDefId for HashMap in the deeply nested module
        let hashmap_def_id = LibraryDefId {
            module: ModulePath::from("std::collections::hash_map"),
            index: 0,
        };
        let hashmap_path = ItemPath::new(
            ModulePath::from("std::collections::hash_map"),
            vec!["HashMap".into()],
        );

        // Add the name -> def_id mapping
        std_lib.names.insert(hashmap_path, hashmap_def_id.clone());

        // Add a scheme for HashMap
        std_lib.schemes.insert(
            hashmap_def_id,
            TyScheme {
                vars: vec![],
                qualifiers: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(ModulePath::from("std"), std_lib);
        db.set_input::<LoadedLibraries>((), libraries);
        setup_no_core(&db);

        // Import std::collections (submodule) and use relative path: collections::hash_map::HashMap
        // This tests that importing a submodule allows relative paths from that submodule
        FileSource::new(
            &db,
            main_file,
            "import std::collections\nfn main() { collections::hash_map::HashMap }".to_string(),
        );

        let resolutions = name_resolutions(&db, main_file);

        // Should have a Def resolution for collections::hash_map::HashMap
        let library_resolutions: Vec<_> = resolutions
            .values()
            .filter(|res| matches!(res, Resolution::Def(DefTarget::Library(_))))
            .collect();

        assert!(
            !library_resolutions.is_empty(),
            "Should resolve 'collections::hash_map::HashMap' (relative to imported submodule std::collections) to DefTarget::Library. Got resolutions: {:?}",
            resolutions
        );
    }
}
