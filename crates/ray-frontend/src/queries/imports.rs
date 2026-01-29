//! Import extraction and resolution queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::ast::{Import, ImportKind};
use ray_query_macros::query;
use ray_shared::{file_id::FileId, pathlib::ModulePath};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        libraries::LoadedLibraries,
        parse::parse_file,
        workspace::{CompilerOptions, WorkspaceSnapshot},
    },
    query::{Database, Query},
};

/// Error that occurs when resolving an import.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImportError {
    /// The imported module does not exist in the workspace or libraries.
    UnknownModule(String),
    /// The import could refer to multiple modules (ambiguous).
    Ambiguous(Vec<ModulePath>),
    /// C imports are not resolved through the module system.
    CImport,
}

/// How names from an import are made accessible.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImportNames {
    /// Namespace handle: access via `module::NAME` (e.g., `import std::io`)
    Namespace,
    /// Selective import: only these names directly accessible (e.g., `import std::io with File`)
    Selective(Vec<String>),
    /// Glob import: all exports directly accessible (e.g., `import std::io with *`)
    Glob,
}

/// A resolved import with its module path and import style.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedImport {
    /// The resolved module path.
    pub module_path: ModulePath,
    /// How names from this module are made accessible.
    pub names: ImportNames,
}

/// Resolve all imports in a file to their target module paths.
///
/// Returns a map from import alias (or module name if no alias) to the resolved
/// import info or an error. Each import produces one entry in the result.
///
/// For `import std::io`, the key is "io", style is Namespace (access via `io::NAME`).
/// For `import std::io with File, Read`, the key is "io", style is Selective(["File", "Read"]).
/// For `import std::io with *`, the key is "io", style is Glob (all names directly accessible).
///
/// When `no_core` is false (the default), implicit glob imports for `core` and `core::io`
/// are automatically injected, unless:
/// - The global `CompilerOptions.no_core` is true, OR
/// - The file has `//![no-core]` in its doc comment, OR
/// - The file is part of the `core` module itself.
#[query]
pub fn resolved_imports(
    db: &Database,
    file_id: FileId,
) -> HashMap<String, Result<ResolvedImport, ImportError>> {
    let imports = file_imports(db, file_id);
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());
    let global_no_core = db.get_input_or_default::<CompilerOptions>(()).no_core;

    let mut result = resolve_imports(&imports, &workspace, &libraries);

    // Inject implicit core imports unless no_core is set globally or per-file
    let per_file_no_core = file_no_core(db, file_id);
    if !global_no_core && !per_file_no_core {
        let file_module = workspace.file_info(file_id).map(|info| &info.module_path);

        // Don't inject core imports into files that are part of core itself
        let is_core_file = file_module
            .map(|mp| mp.starts_with("core"))
            .unwrap_or(false);

        if !is_core_file {
            inject_implicit_imports(&mut result, &workspace, &libraries);
        }
    }

    result
}

/// Extract all import statements from a file.
#[query]
pub fn file_imports(db: &Database, file_id: FileId) -> Vec<Import> {
    let parse_result = parse_file(db, file_id);
    parse_result.ast.imports
}

/// Check if a file has the `//![no-core]` directive in its doc comment.
///
/// This is a per-file opt-out of implicit core imports. When present,
/// the file will not receive automatic `import core with *` and `import core::io with *`.
#[query]
pub fn file_no_core(db: &Database, file_id: FileId) -> bool {
    let parse_result = parse_file(db, file_id);
    parse_result
        .ast
        .doc_comment
        .as_ref()
        .map(|doc| doc.contains("[no-core]"))
        .unwrap_or(false)
}

/// Inject implicit glob imports for `core` and `core::io`.
fn inject_implicit_imports(
    result: &mut HashMap<String, Result<ResolvedImport, ImportError>>,
    workspace: &WorkspaceSnapshot,
    libraries: &LoadedLibraries,
) {
    // Inject `import core with *` (keyed by "core")
    // Only if user hasn't explicitly imported something with alias "core"
    if !result.contains_key("core") {
        let core_path = ModulePath::from("core");
        if let Ok(mp) = resolve_module_path(&core_path, workspace, libraries) {
            result.insert(
                "core".to_string(),
                Ok(ResolvedImport {
                    module_path: mp,
                    names: ImportNames::Glob,
                }),
            );
        }
    }

    // Inject `import core::io with *` (keyed by "io")
    // Only if user hasn't explicitly imported something with alias "io"
    if !result.contains_key("io") {
        let io_path = ModulePath::from("core::io");
        if let Ok(mp) = resolve_module_path(&io_path, workspace, libraries) {
            result.insert(
                "io".to_string(),
                Ok(ResolvedImport {
                    module_path: mp,
                    names: ImportNames::Glob,
                }),
            );
        }
    }
}

/// Resolve a list of imports against a workspace and loaded libraries.
fn resolve_imports(
    imports: &[Import],
    workspace: &WorkspaceSnapshot,
    libraries: &LoadedLibraries,
) -> HashMap<String, Result<ResolvedImport, ImportError>> {
    let mut result = HashMap::new();

    for import in imports {
        match &import.kind {
            ImportKind::Path(path_node) => {
                // `import foo::bar` - namespace handle, access via `bar::NAME`
                let path = &path_node.value;
                let alias = path.to_short_name();
                let module_path = ModulePath::from(path);
                let resolution =
                    resolve_module_path(&module_path, workspace, libraries).map(|mp| {
                        ResolvedImport {
                            module_path: mp,
                            names: ImportNames::Namespace,
                        }
                    });
                result.insert(alias, resolution);
            }
            ImportKind::Names(path_node, names) => {
                // `import foo::bar with X, Y` - selective import
                let path = &path_node.value;
                let alias = path.to_short_name();
                let module_path = ModulePath::from(path);
                let name_strings: Vec<String> = names.iter().map(|n| n.to_string()).collect();
                let resolution =
                    resolve_module_path(&module_path, workspace, libraries).map(|mp| {
                        ResolvedImport {
                            module_path: mp,
                            names: ImportNames::Selective(name_strings),
                        }
                    });
                result.insert(alias, resolution);
            }
            ImportKind::Glob(path_node) => {
                // `import foo::bar with *` - glob import
                let path = &path_node.value;
                let alias = path.to_short_name();
                let module_path = ModulePath::from(path);
                let resolution =
                    resolve_module_path(&module_path, workspace, libraries).map(|mp| {
                        ResolvedImport {
                            module_path: mp,
                            names: ImportNames::Glob,
                        }
                    });
                result.insert(alias, resolution);
            }
            ImportKind::CImport(name, _) => {
                // C imports don't resolve to module paths
                result.insert(name.clone(), Err(ImportError::CImport));
            }
        }
    }

    result
}

/// Resolve a single module path against the workspace and loaded libraries.
fn resolve_module_path(
    module_path: &ModulePath,
    workspace: &WorkspaceSnapshot,
    libraries: &LoadedLibraries,
) -> Result<ModulePath, ImportError> {
    // Check if the module exists in the workspace
    if workspace.module_info(module_path).is_some() {
        return Ok(module_path.clone());
    }

    // Check if the module exists in loaded libraries
    if libraries.has_module(&module_path) {
        return Ok(module_path.clone());
    }

    // Module not found
    Err(ImportError::UnknownModule(module_path.to_string()))
}

#[cfg(test)]
mod tests {
    use ray_core::ast::ImportKind;
    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            imports::{ImportError, ImportNames, file_imports, file_no_core, resolved_imports},
            libraries::{LibraryData, LoadedLibraries},
            workspace::{CompilerOptions, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
    }

    /// Helper to set up CompilerOptions with no_core = true (no implicit imports).
    fn setup_no_core(db: &Database) {
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: true });
    }

    /// Helper to set up CompilerOptions with no_core = false (with implicit imports).
    fn setup_with_core(db: &Database) {
        db.set_input::<CompilerOptions>((), CompilerOptions { no_core: false });
    }

    #[test]
    fn file_imports_returns_empty_for_no_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let imports = file_imports(&db, file_id);

        assert!(imports.is_empty());
    }

    #[test]
    fn file_imports_extracts_path_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "import std::io\nfn main() {}".to_string());

        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 1);
    }

    #[test]
    fn file_imports_extracts_multiple_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "import std::io\nimport std::collections\nfn main() {}".to_string(),
        );

        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 2);
    }

    #[test]
    fn file_imports_extracts_named_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "import std::io with File, Read\nfn main() {}".to_string(),
        );

        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 1);
    }

    #[test]
    fn file_imports_extracts_glob_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "import std::io with *\nfn main() {}".to_string(),
        );

        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 1);
        assert!(
            matches!(imports[0].kind, ImportKind::Glob(_)),
            "Expected glob import"
        );
    }

    #[test]
    fn resolved_imports_handles_glob_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let io_file = workspace.add_file(
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, io_file, "fn read() {}".to_string());
        FileSource::new(&db, file_id, "import std::io with *".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let io_result = result.get("io").expect("should have io import");
        assert!(io_result.is_ok());
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "std::io");
        assert_eq!(resolved.names, ImportNames::Glob);
    }

    #[test]
    fn resolved_imports_returns_empty_for_no_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let result = resolved_imports(&db, file_id);

        assert!(result.is_empty());
    }

    #[test]
    fn resolved_imports_resolves_existing_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create a module "utils" with a file
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        // Create the main file that imports utils
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileSource::new(&db, file_id, "import utils".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let utils_result = result.get("utils").expect("should have utils import");
        assert!(utils_result.is_ok());
        let resolved = utils_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "utils");
        assert_eq!(resolved.names, ImportNames::Namespace);
    }

    #[test]
    fn resolved_imports_returns_error_for_unknown_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, file_id, "import nonexistent".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let import_result = result.get("nonexistent").expect("should have import");
        assert!(matches!(
            import_result,
            Err(ImportError::UnknownModule(name)) if name == "nonexistent"
        ));
    }

    #[test]
    fn resolved_imports_handles_nested_module_path() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create a nested module "std::io"
        let io_file = workspace.add_file(
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, io_file, "fn read() {}".to_string());
        FileSource::new(&db, file_id, "import std::io".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        // The alias is the last component "io"
        let io_result = result.get("io").expect("should have io import");
        assert!(io_result.is_ok());
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "std::io");
        assert_eq!(resolved.names, ImportNames::Namespace);
    }

    #[test]
    fn resolved_imports_handles_named_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let io_file = workspace.add_file(
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, io_file, "fn read() {}".to_string());
        FileSource::new(&db, file_id, "import std::io with File, Read".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        // The module path is resolved, named imports are just names to bring into scope
        let io_result = result.get("io").expect("should have io import");
        assert!(io_result.is_ok());
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "std::io");
        assert_eq!(
            resolved.names,
            ImportNames::Selective(vec!["File".to_string(), "Read".to_string()])
        );
    }

    #[test]
    fn resolved_imports_handles_multiple_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let io_file = workspace.add_file(
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        let collections_file = workspace.add_file(
            FilePath::from("std/collections/mod.ray"),
            ModulePath::from("std::collections"),
        );
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, io_file, "fn read() {}".to_string());
        FileSource::new(&db, collections_file, "struct List {}".to_string());
        FileSource::new(
            &db,
            file_id,
            "import std::io\nimport std::collections".to_string(),
        );

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 2);
        assert!(result.get("io").unwrap().is_ok());
        assert!(result.get("collections").unwrap().is_ok());
    }

    #[test]
    fn resolved_imports_resolves_library_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_no_core(&db);

        // Set up a library with core::io module
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        FileSource::new(&db, file_id, "import core::io".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let io_result = result.get("io").expect("should have io import");
        assert!(io_result.is_ok(), "Library module should resolve");
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "core::io");
    }

    #[test]
    fn resolved_imports_resolves_library_root() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_no_core(&db);

        // Set up a library with core as the root
        let mut libraries = LoadedLibraries::default();
        let core_lib = LibraryData::default();
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        FileSource::new(&db, file_id, "import core".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let core_result = result.get("core").expect("should have core import");
        assert!(core_result.is_ok(), "Library root should resolve");
        let resolved = core_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "core");
    }

    // Tests for implicit core imports

    #[test]
    fn resolved_imports_injects_implicit_core_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up libraries with core and core::io
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        setup_with_core(&db); // no_core = false

        // File has no explicit imports
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let result = resolved_imports(&db, file_id);

        // Should have implicit imports for core and core::io
        assert_eq!(result.len(), 2);

        let core_result = result
            .get("core")
            .expect("should have implicit core import");
        assert!(core_result.is_ok());
        let resolved = core_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "core");
        assert_eq!(resolved.names, ImportNames::Glob);

        let io_result = result
            .get("io")
            .expect("should have implicit core::io import");
        assert!(io_result.is_ok());
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "core::io");
        assert_eq!(resolved.names, ImportNames::Glob);
    }

    #[test]
    fn resolved_imports_no_core_disables_implicit_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up libraries with core and core::io
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        setup_no_core(&db); // no_core = true

        // File has no explicit imports
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let result = resolved_imports(&db, file_id);

        // Should have no imports
        assert!(result.is_empty());
    }

    #[test]
    fn resolved_imports_skips_implicit_for_core_files() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // File is part of core module
        let file_id =
            workspace.add_file(FilePath::from("core/string.ray"), ModulePath::from("core"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up libraries with core and core::io
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        setup_with_core(&db); // no_core = false

        // Core file has no explicit imports
        FileSource::new(&db, file_id, "struct string {}".to_string());

        let result = resolved_imports(&db, file_id);

        // Should have no implicit imports (file is in core module)
        assert!(result.is_empty());
    }

    #[test]
    fn resolved_imports_skips_implicit_for_core_io_files() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // File is part of core::io module
        let file_id = workspace.add_file(
            FilePath::from("core/io/mod.ray"),
            ModulePath::from("core::io"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up libraries with core and core::io
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        setup_with_core(&db); // no_core = false

        FileSource::new(&db, file_id, "fn print() {}".to_string());

        let result = resolved_imports(&db, file_id);

        // Should have no implicit imports (file is in core::io module)
        assert!(result.is_empty());
    }

    #[test]
    fn resolved_imports_explicit_import_shadows_implicit() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create a user module named "io"
        let user_io_file = workspace.add_file(
            FilePath::from("myproject/io/mod.ray"),
            ModulePath::from("myproject::io"),
        );
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("myproject"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up libraries with core and core::io
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        setup_with_core(&db);

        FileSource::new(&db, user_io_file, "fn custom_read() {}".to_string());
        // Explicitly import myproject::io (alias is "io")
        FileSource::new(&db, file_id, "import myproject::io".to_string());

        let result = resolved_imports(&db, file_id);

        // Should have core (implicit) and io (explicit, shadows core::io)
        assert_eq!(result.len(), 2);

        // "io" should be the explicit import, not implicit core::io
        let io_result = result.get("io").expect("should have io import");
        assert!(io_result.is_ok());
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "myproject::io");
        assert_eq!(
            resolved.names,
            ImportNames::Namespace,
            "Explicit import should be Namespace, not Glob"
        );
    }

    // Tests for per-file //![no-core] directive

    #[test]
    fn file_no_core_returns_false_for_no_doc_comment() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        assert!(!file_no_core(&db, file_id));
    }

    #[test]
    fn file_no_core_returns_false_for_unrelated_doc_comment() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "//! This is just a normal doc comment\nfn main() {}".to_string(),
        );

        assert!(!file_no_core(&db, file_id));
    }

    #[test]
    fn file_no_core_returns_true_for_no_core_directive() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "//![no-core]\nfn main() {}".to_string());

        assert!(file_no_core(&db, file_id));
    }

    #[test]
    fn file_no_core_returns_true_when_embedded_in_doc_comment() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(
            &db,
            file_id,
            "//! Module documentation\n//![no-core]\n//! More docs\nfn main() {}".to_string(),
        );

        assert!(file_no_core(&db, file_id));
    }

    #[test]
    fn resolved_imports_respects_per_file_no_core() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up libraries with core and core::io
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::io"));
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        setup_with_core(&db); // Global no_core = false

        // File has [no-core] directive
        FileSource::new(&db, file_id, "//![no-core]\nfn main() {}".to_string());

        let result = resolved_imports(&db, file_id);

        // Should have no imports due to per-file [no-core]
        assert!(
            result.is_empty(),
            "Per-file [no-core] should disable implicit imports"
        );
    }

    #[test]
    fn resolved_imports_per_file_no_core_still_allows_explicit_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up libraries with core
        let mut libraries = LoadedLibraries::default();
        let core_lib = LibraryData::default();
        libraries.add(ModulePath::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        setup_with_core(&db); // Global no_core = false

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        // File has [no-core] but explicit import
        FileSource::new(
            &db,
            file_id,
            "//![no-core]\nimport utils\nfn main() {}".to_string(),
        );

        let result = resolved_imports(&db, file_id);

        // Should have only the explicit import, not implicit core imports
        assert_eq!(result.len(), 1);
        assert!(result.contains_key("utils"));
        assert!(!result.contains_key("core"));
        assert!(!result.contains_key("io"));
    }
}
