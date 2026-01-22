//! Name resolution query for the incremental compiler.

use std::collections::HashMap;

use ray_core::sema::resolve_names_in_file;
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId,
    node_id::NodeId,
    pathlib::{ModulePath, Path},
    resolution::{DefTarget, Resolution},
};

use crate::{
    queries::{
        exports::{ExportedItem, file_exports, module_def_index},
        imports::resolved_imports,
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
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());

    // Get file info to know which module this file belongs to
    let file_info = match workspace.file_info(file_id) {
        Some(info) => info,
        None => return HashMap::new(),
    };

    // Get exports from the file's module (including this file's exports)
    let module_index = module_def_index(db, file_info.module_path.clone());

    // Convert module_index to HashMap<String, DefTarget> for resolve_names_in_file
    let module_exports = convert_to_def_targets(&module_index);

    // Compute sibling exports: exports from other files in the same module
    let sibling_exports = compute_sibling_exports(db, file_id, &file_info.module_path, &workspace);

    // Build imports map: alias -> module_path
    let mut imports_map: HashMap<String, ModulePath> = HashMap::new();

    // Also build combined_exports for unqualified access
    let mut combined_exports = module_exports;

    for (alias, import_result) in &resolved {
        if let Ok(resolved_import) = import_result {
            match &resolved_import.names {
                None => {
                    // Plain import: `import utils` enables `utils::foo` (qualified access only)
                    imports_map.insert(alias.clone(), resolved_import.module_path.clone());
                }
                Some(names) => {
                    // Selective import: `import utils with foo` enables `foo` (unqualified only)
                    // Does NOT enable `utils::foo`
                    let module_path = &resolved_import.module_path;

                    // Check if this is a library import or workspace import
                    let imported_exports =
                        if libraries.library_for_module(&module_path.to_path()).is_some() {
                            // Library import - get exports from library
                            get_library_exports(&libraries, module_path)
                        } else {
                            // Workspace import
                            let imported_module_index = module_def_index(db, module_path.to_path());
                            convert_to_def_targets(&imported_module_index)
                        };

                    for name in names {
                        if let Some(target) = imported_exports.get(name) {
                            combined_exports
                                .entry(name.clone())
                                .or_insert(target.clone());
                        }
                    }
                }
            }
        }
    }

    // Create closure to look up exports for an import alias
    let import_exports = |alias: &str| -> Option<HashMap<String, DefTarget>> {
        let module_path = imports_map.get(alias)?;

        // Check if this is a library import or workspace import
        if libraries.library_for_module(&module_path.to_path()).is_some() {
            // Library import - get exports from library
            Some(get_library_exports(&libraries, module_path))
        } else {
            // Workspace import
            let imported_module_index = module_def_index(db, module_path.to_path());
            Some(convert_to_def_targets(&imported_module_index))
        }
    };

    resolve_names_in_file(
        &parse_result.ast,
        &imports_map,
        &combined_exports,
        &sibling_exports,
        import_exports,
    )
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
    let lib_path = match libraries.library_for_module(&module_path.to_path()) {
        Some(path) => path.clone(),
        None => return result,
    };

    // Get the library data
    let lib_data = match libraries.get(&lib_path) {
        Some(data) => data,
        None => return result,
    };

    // Collect exports from the library's schemes
    // The scheme paths are full paths like "core::io::read", we need to filter
    // for paths that start with the module_path
    let module_prefix = module_path.to_string();

    for (scheme_path, _scheme) in &lib_data.schemes {
        let path_str = scheme_path.to_string();
        // Check if this path belongs to the imported module
        if path_str.starts_with(&module_prefix) {
            // Extract the name: for "core::io::read" with module "core::io", name is "read"
            let suffix = &path_str[module_prefix.len()..];
            if let Some(name) = suffix.strip_prefix("::") {
                // Only direct children (no more :: in the name)
                if !name.contains("::") {
                    result.insert(
                        name.to_string(),
                        DefTarget::Library {
                            lib: lib_path.clone(),
                            path: scheme_path.clone(),
                        },
                    );
                }
            }
        }
    }

    // Also collect struct exports
    for lib_struct in &lib_data.structs {
        let path_str = lib_struct.path.to_string();
        if path_str.starts_with(&module_prefix) {
            let suffix = &path_str[module_prefix.len()..];
            if let Some(name) = suffix.strip_prefix("::") {
                if !name.contains("::") {
                    result.insert(
                        name.to_string(),
                        DefTarget::Library {
                            lib: lib_path.clone(),
                            path: lib_struct.path.clone(),
                        },
                    );
                }
            }
        }
    }

    // Also collect trait exports
    for lib_trait in &lib_data.traits {
        let path_str = lib_trait.path.to_string();
        if path_str.starts_with(&module_prefix) {
            let suffix = &path_str[module_prefix.len()..];
            if let Some(name) = suffix.strip_prefix("::") {
                if !name.contains("::") {
                    result.insert(
                        name.to_string(),
                        DefTarget::Library {
                            lib: lib_path.clone(),
                            path: lib_trait.path.clone(),
                        },
                    );
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
    module_path: &Path,
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
    use ray_shared::{
        pathlib::{FilePath, Path},
        resolution::{DefTarget, Resolution},
    };

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            resolve::name_resolutions,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
    }

    #[test]
    fn name_resolutions_returns_empty_for_empty_file() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
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
    fn name_resolutions_resolves_library_import_qualified() {
        use crate::queries::libraries::{LibraryData, LibraryScheme};
        use ray_shared::ty::Ty;

        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::io module containing a "read" function
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(Path::from("core::io"));
        // Add a scheme for core::io::read
        core_lib.schemes.insert(
            Path::from("core::io::read"),
            LibraryScheme {
                vars: vec![],
                predicates: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(Path::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

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
            .filter(|res| {
                matches!(
                    res,
                    Resolution::Def(DefTarget::Library { lib, path })
                    if lib.to_string() == "core" && path.to_string() == "core::io::read"
                )
            })
            .collect();

        assert_eq!(
            library_resolutions.len(),
            1,
            "Should resolve qualified library import 'io::read' to DefTarget::Library"
        );
    }

    #[test]
    fn name_resolutions_resolves_library_selective_import() {
        use crate::queries::libraries::{LibraryData, LibraryScheme};
        use ray_shared::ty::Ty;

        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let main_file = workspace.add_file(FilePath::from("main.ray"), Path::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::io module containing "read" and "write" functions
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(Path::from("core::io"));
        core_lib.schemes.insert(
            Path::from("core::io::read"),
            LibraryScheme {
                vars: vec![],
                predicates: vec![],
                ty: Ty::unit(),
            },
        );
        core_lib.schemes.insert(
            Path::from("core::io::write"),
            LibraryScheme {
                vars: vec![],
                predicates: vec![],
                ty: Ty::unit(),
            },
        );
        libraries.add(Path::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

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
            .filter(|res| matches!(res, Resolution::Def(DefTarget::Library { .. })))
            .count();

        assert_eq!(
            library_count, 1,
            "Selective library import should only bring 'read' into scope, not 'write'"
        );
    }
}
