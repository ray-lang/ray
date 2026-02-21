//! Import extraction and resolution queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::ast::{Decl, Export, ExportKind, Import, ImportKind};
use ray_query_macros::query;
use ray_shared::{file_id::FileId, node_id::NodeId, pathlib::ModulePath};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        libraries::LoadedLibraries,
        parse::parse_file_raw,
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

    let file_module = workspace
        .file_info(file_id)
        .map(|info| info.module_path.clone());
    let mut result = resolve_imports(&imports, &workspace, &libraries, file_module.as_ref());

    // Inject implicit core imports unless no_core is set globally or per-file
    let per_file_no_core = file_no_core(db, file_id);
    if !global_no_core && !per_file_no_core {
        // Don't inject core imports into files that are part of core itself
        let is_core_file = file_module
            .as_ref()
            .map(|mp| mp.starts_with("core"))
            .unwrap_or(false);

        if !is_core_file {
            inject_implicit_imports(&mut result, &workspace, &libraries);
        }
    }

    // Inject `import testing with *` when file has test blocks
    let parse_result = parse_file_raw(db, file_id);
    let has_tests = parse_result
        .ast
        .decls
        .iter()
        .any(|d| matches!(d.value, Decl::Test(_)));
    if has_tests {
        inject_testing_import(&mut result, &workspace, &libraries);
    }

    result
}

/// Extract all import statements from a file.
#[query]
pub fn file_imports(db: &Database, file_id: FileId) -> Vec<Import> {
    let parse_result = parse_file_raw(db, file_id);
    parse_result.ast.imports.clone()
}

/// Check if a file has the `//![no-core]` directive in its doc comment.
///
/// This is a per-file opt-out of implicit core imports. When present,
/// the file will not receive automatic `import core with *` and `import core::io with *`.
#[query]
pub fn file_no_core(db: &Database, file_id: FileId) -> bool {
    let parse_result = parse_file_raw(db, file_id);
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
        if let Ok(mp) = resolve_module_path(&core_path, workspace, libraries, None) {
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
        if let Ok(mp) = resolve_module_path(&io_path, workspace, libraries, None) {
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

/// Inject `import testing with *` for files containing test blocks.
///
/// Only injected when the `testing` module is available in the workspace or libraries.
fn inject_testing_import(
    result: &mut HashMap<String, Result<ResolvedImport, ImportError>>,
    workspace: &WorkspaceSnapshot,
    libraries: &LoadedLibraries,
) {
    if !result.contains_key("testing") {
        let testing_path = ModulePath::from("testing");
        if let Ok(mp) = resolve_module_path(&testing_path, workspace, libraries, None) {
            result.insert(
                "testing".to_string(),
                Ok(ResolvedImport {
                    module_path: mp,
                    names: ImportNames::Glob,
                }),
            );
        }
    }
}

/// What a NodeId in an import/export statement points to.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImportExportTarget {
    /// A module path node (e.g., `core::io` in `import core::io`).
    Module(ModulePath),
    /// A specific name from a module (e.g., `read` in `import core::io with read`).
    ModuleName { module: ModulePath, name: String },
}

/// Build an index mapping NodeIds in import/export statements to their resolved targets.
///
/// For each import and export statement, maps:
/// - The module path `Node<Path>` → `ImportExportTarget::Module(resolved_module_path)`
/// - Each selective name `Node<Path>` → `ImportExportTarget::ModuleName { module, name }`
///
/// This is used by the LSP for hover and go-to-definition on import/export statements.
#[query]
pub fn import_export_targets(
    db: &Database,
    file_id: FileId,
) -> HashMap<NodeId, ImportExportTarget> {
    let mut targets = HashMap::new();

    // Process imports
    let imports = file_imports(db, file_id);
    let resolved = resolved_imports(db, file_id);

    for import in &imports {
        collect_import_targets(import, &resolved, &mut targets);
    }

    // Process exports
    let parse_result = parse_file_raw(db, file_id);
    let reexports = crate::queries::exports::file_reexports(db, file_id);

    for (export, reexport) in parse_result.ast.exports.iter().zip(reexports.iter()) {
        collect_export_targets(export, reexport, &mut targets);
    }

    targets
}

/// Collect targets from a single import statement.
fn collect_import_targets(
    import: &Import,
    resolved: &HashMap<String, Result<ResolvedImport, ImportError>>,
    targets: &mut HashMap<NodeId, ImportExportTarget>,
) {
    match &import.kind {
        ImportKind::Path(path_node) => {
            let alias = path_node.value.to_short_name();
            if let Some(Ok(resolved_import)) = resolved.get(&alias) {
                targets.insert(
                    path_node.id,
                    ImportExportTarget::Module(resolved_import.module_path.clone()),
                );
            }
        }
        ImportKind::Names(path_node, name_nodes) => {
            let alias = path_node.value.to_short_name();
            if let Some(Ok(resolved_import)) = resolved.get(&alias) {
                let mp = &resolved_import.module_path;
                targets.insert(path_node.id, ImportExportTarget::Module(mp.clone()));
                for name_node in name_nodes {
                    let name = name_node.value.to_short_name();
                    targets.insert(
                        name_node.id,
                        ImportExportTarget::ModuleName {
                            module: mp.clone(),
                            name,
                        },
                    );
                }
            }
        }
        ImportKind::Glob(path_node) => {
            let alias = path_node.value.to_short_name();
            if let Some(Ok(resolved_import)) = resolved.get(&alias) {
                targets.insert(
                    path_node.id,
                    ImportExportTarget::Module(resolved_import.module_path.clone()),
                );
            }
        }
        ImportKind::CImport(_, _) | ImportKind::Incomplete => {}
    }
}

/// Collect targets from a single export statement.
fn collect_export_targets(
    export: &Export,
    reexport: &crate::queries::exports::ResolvedReExport,
    targets: &mut HashMap<NodeId, ImportExportTarget>,
) {
    let mp = &reexport.module_path;
    match &export.kind {
        ExportKind::Path(path_node) => {
            targets.insert(path_node.id, ImportExportTarget::Module(mp.clone()));
        }
        ExportKind::Names(path_node, name_nodes) => {
            targets.insert(path_node.id, ImportExportTarget::Module(mp.clone()));
            for name_node in name_nodes {
                let name = name_node.value.to_short_name();
                targets.insert(
                    name_node.id,
                    ImportExportTarget::ModuleName {
                        module: mp.clone(),
                        name,
                    },
                );
            }
        }
        ExportKind::Glob(path_node) => {
            targets.insert(path_node.id, ImportExportTarget::Module(mp.clone()));
        }
        ExportKind::Incomplete => {}
    }
}

/// Resolve a list of imports against a workspace and loaded libraries.
///
/// `current_module` is the module containing the imports, used to resolve `super`.
fn resolve_imports(
    imports: &[Import],
    workspace: &WorkspaceSnapshot,
    libraries: &LoadedLibraries,
    current_module: Option<&ModulePath>,
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
                    resolve_module_path(&module_path, workspace, libraries, current_module).map(
                        |mp| ResolvedImport {
                            module_path: mp,
                            names: ImportNames::Namespace,
                        },
                    );
                result.insert(alias, resolution);
            }
            ImportKind::Names(path_node, names) => {
                // `import foo::bar with X, Y` - selective import
                let path = &path_node.value;
                let alias = path.to_short_name();
                let module_path = ModulePath::from(path);
                let name_strings: Vec<String> = names.iter().map(|n| n.to_string()).collect();
                let resolution =
                    resolve_module_path(&module_path, workspace, libraries, current_module).map(
                        |mp| ResolvedImport {
                            module_path: mp,
                            names: ImportNames::Selective(name_strings),
                        },
                    );
                result.insert(alias, resolution);
            }
            ImportKind::Glob(path_node) => {
                // `import foo::bar with *` - glob import
                let path = &path_node.value;
                let alias = path.to_short_name();
                let module_path = ModulePath::from(path);
                let resolution =
                    resolve_module_path(&module_path, workspace, libraries, current_module).map(
                        |mp| ResolvedImport {
                            module_path: mp,
                            names: ImportNames::Glob,
                        },
                    );
                result.insert(alias, resolution);
            }
            ImportKind::CImport(name, _) => {
                // C imports don't resolve to module paths
                result.insert(name.clone(), Err(ImportError::CImport));
            }
            ImportKind::Incomplete => {
                // Error recovery artifact — skip
            }
        }
    }

    result
}

/// Resolve a single module path against the workspace and loaded libraries.
///
/// If the path contains `super` segments, they are resolved relative to
/// `current_module` before lookup.
pub(crate) fn resolve_module_path(
    module_path: &ModulePath,
    workspace: &WorkspaceSnapshot,
    libraries: &LoadedLibraries,
    current_module: Option<&ModulePath>,
) -> Result<ModulePath, ImportError> {
    // Resolve `super` segments if present
    let resolved = if module_path.has_super() {
        if let Some(current) = current_module {
            module_path.resolve_super(current)
        } else {
            return Err(ImportError::UnknownModule(module_path.to_string()));
        }
    } else {
        module_path.clone()
    };

    // Check if the module exists in the workspace
    if workspace.module_info(&resolved).is_some() {
        return Ok(resolved);
    }

    // Check if the module exists in loaded libraries
    if libraries.has_module(&resolved) {
        return Ok(resolved);
    }

    // Try relative child resolution: if the current module is `core` and the import
    // is `io`, try resolving `core::io`.
    if let Some(current) = current_module {
        let mut child_segments = current.segments().to_vec();
        child_segments.extend(resolved.segments().iter().cloned());
        let child_path = ModulePath::new(child_segments);

        if workspace.module_info(&child_path).is_some() {
            return Ok(child_path);
        }

        if libraries.has_module(&child_path) {
            return Ok(child_path);
        }
    }

    // Try sibling resolution: if the current module is `mymod::utils` and the import
    // is `helpers`, try resolving `mymod::helpers`.
    if let Some(current) = current_module {
        let segments = current.segments();
        if segments.len() > 1 {
            let parent = &segments[..segments.len() - 1];
            let mut sibling = parent.to_vec();
            sibling.extend(resolved.segments().iter().cloned());
            let sibling_path = ModulePath::new(sibling);

            if workspace.module_info(&sibling_path).is_some() {
                return Ok(sibling_path);
            }

            if libraries.has_module(&sibling_path) {
                return Ok(sibling_path);
            }
        }
    }

    // Module not found
    Err(ImportError::UnknownModule(resolved.to_string()))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_core::ast::{ExportKind, ImportKind};
    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            imports::{
                ImportError, ImportExportTarget, ImportNames, file_imports, file_no_core,
                import_export_targets, resolved_imports,
            },
            libraries::{LibraryData, LoadedLibraries},
            parse::parse_file_raw,
            workspace::{CompilerOptions, FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    /// Helper to set up CompilerOptions with no_core = true (no implicit imports).
    fn setup_no_core(db: &Database) {
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: true,
                test_mode: false,
            },
        );
    }

    /// Helper to set up CompilerOptions with no_core = false (with implicit imports).
    fn setup_with_core(db: &Database) {
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: false,
                test_mode: false,
            },
        );
    }

    #[test]
    fn file_imports_returns_empty_for_no_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), ModulePath::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
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
        FileMetadata::new(
            &db,
            io_file,
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        FileSource::new(&db, file_id, "import std::io with *".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

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
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "import utils".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

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
        FileMetadata::new(
            &db,
            io_file,
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        FileSource::new(&db, file_id, "import std::io".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        FileMetadata::new(
            &db,
            io_file,
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        FileSource::new(&db, file_id, "import std::io with File, Read".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        FileMetadata::new(
            &db,
            io_file,
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        FileSource::new(&db, collections_file, "struct List {}".to_string());
        FileMetadata::new(
            &db,
            collections_file,
            FilePath::from("std/collections/mod.ray"),
            ModulePath::from("std::collections"),
        );
        FileSource::new(
            &db,
            file_id,
            "import std::io\nimport std::collections".to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
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
        db.set_input::<LoadedLibraries>((), libraries);

        FileSource::new(&db, file_id, "import core::io".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        db.set_input::<LoadedLibraries>((), libraries);

        FileSource::new(&db, file_id, "import core".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        db.set_input::<LoadedLibraries>((), libraries);

        setup_with_core(&db); // no_core = false

        // File has no explicit imports
        FileSource::new(&db, file_id, "fn main() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        db.set_input::<LoadedLibraries>((), libraries);

        setup_no_core(&db); // no_core = true

        // File has no explicit imports
        FileSource::new(&db, file_id, "fn main() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        db.set_input::<LoadedLibraries>((), libraries);

        setup_with_core(&db); // no_core = false

        // Core file has no explicit imports
        FileSource::new(&db, file_id, "struct string {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        db.set_input::<LoadedLibraries>((), libraries);

        setup_with_core(&db); // no_core = false

        FileSource::new(&db, file_id, "fn print() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("core/io/mod.ray"),
            ModulePath::from("core::io"),
        );

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
        db.set_input::<LoadedLibraries>((), libraries);

        setup_with_core(&db);

        FileSource::new(&db, user_io_file, "fn custom_read() {}".to_string());
        FileMetadata::new(
            &db,
            user_io_file,
            FilePath::from("myproject/io/mod.ray"),
            ModulePath::from("myproject::io"),
        );
        // Explicitly import myproject::io (alias is "io")
        FileSource::new(&db, file_id, "import myproject::io".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("myproject"),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
        );

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
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test.ray"),
            ModulePath::from("test"),
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
        db.set_input::<LoadedLibraries>((), libraries);

        setup_with_core(&db); // Global no_core = false

        // File has [no-core] directive
        FileSource::new(&db, file_id, "//![no-core]\nfn main() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

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
        db.set_input::<LoadedLibraries>((), libraries);

        setup_with_core(&db); // Global no_core = false

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        // File has [no-core] but explicit import
        FileSource::new(
            &db,
            file_id,
            "//![no-core]\nimport utils\nfn main() {}".to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let result = resolved_imports(&db, file_id);

        // Should have only the explicit import, not implicit core imports
        assert_eq!(result.len(), 1);
        assert!(result.contains_key("utils"));
        assert!(!result.contains_key("core"));
        assert!(!result.contains_key("io"));
    }

    // =========================================================================
    // Sibling resolution tests (file = module)
    // =========================================================================

    #[test]
    fn resolved_imports_sibling_resolution_resolves_sibling_module() {
        // From mymod::utils, `import helpers` should resolve to mymod::helpers
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let helpers_file = workspace.add_file(
            FilePath::from("mymod/helpers.ray"),
            ModulePath::from("mymod::helpers"),
        );
        let utils_file = workspace.add_file(
            FilePath::from("mymod/utils.ray"),
            ModulePath::from("mymod::utils"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, helpers_file, "fn help() {}".to_string());
        FileMetadata::new(
            &db,
            helpers_file,
            FilePath::from("mymod/helpers.ray"),
            ModulePath::from("mymod::helpers"),
        );
        // utils imports helpers (sibling resolution: mymod::utils → mymod::helpers)
        FileSource::new(&db, utils_file, "import helpers".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("mymod/utils.ray"),
            ModulePath::from("mymod::utils"),
        );

        let result = resolved_imports(&db, utils_file);

        assert_eq!(result.len(), 1);
        let helpers_result = result.get("helpers").expect("should have helpers import");
        assert!(helpers_result.is_ok(), "sibling import should resolve");
        let resolved = helpers_result.as_ref().unwrap();
        assert_eq!(
            resolved.module_path.to_string(),
            "mymod::helpers",
            "should resolve to full sibling path"
        );
        assert_eq!(resolved.names, ImportNames::Namespace);
    }

    #[test]
    fn resolved_imports_sibling_resolution_selective() {
        // From mymod::utils, `import helpers with help` resolves as selective sibling import
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let helpers_file = workspace.add_file(
            FilePath::from("mymod/helpers.ray"),
            ModulePath::from("mymod::helpers"),
        );
        let utils_file = workspace.add_file(
            FilePath::from("mymod/utils.ray"),
            ModulePath::from("mymod::utils"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, helpers_file, "fn help() {}".to_string());
        FileMetadata::new(
            &db,
            helpers_file,
            FilePath::from("mymod/helpers.ray"),
            ModulePath::from("mymod::helpers"),
        );
        FileSource::new(&db, utils_file, "import helpers with help".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("mymod/utils.ray"),
            ModulePath::from("mymod::utils"),
        );

        let result = resolved_imports(&db, utils_file);

        assert_eq!(result.len(), 1);
        let helpers_result = result.get("helpers").unwrap();
        assert!(helpers_result.is_ok());
        let resolved = helpers_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "mymod::helpers");
        assert_eq!(
            resolved.names,
            ImportNames::Selective(vec!["help".to_string()])
        );
    }

    #[test]
    fn resolved_imports_sibling_resolution_not_for_top_level() {
        // From a top-level module (1 segment), sibling resolution should NOT apply
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, file_id, "import nonexistent".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let import_result = result.get("nonexistent").unwrap();
        assert!(
            import_result.is_err(),
            "top-level module should not use sibling resolution"
        );
    }

    #[test]
    fn resolved_imports_child_resolution_takes_priority_over_sibling() {
        // If both child and sibling exist, child should win
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // child: mymod::utils::sub
        let child_file = workspace.add_file(
            FilePath::from("mymod/utils/sub/mod.ray"),
            ModulePath::from("mymod::utils::sub"),
        );
        // sibling: mymod::sub
        let sibling_file = workspace.add_file(
            FilePath::from("mymod/sub.ray"),
            ModulePath::from("mymod::sub"),
        );
        let utils_file = workspace.add_file(
            FilePath::from("mymod/utils/mod.ray"),
            ModulePath::from("mymod::utils"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, child_file, "fn child_fn() {}".to_string());
        FileMetadata::new(
            &db,
            child_file,
            FilePath::from("mymod/utils/sub/mod.ray"),
            ModulePath::from("mymod::utils::sub"),
        );
        FileSource::new(&db, sibling_file, "fn sibling_fn() {}".to_string());
        FileMetadata::new(
            &db,
            sibling_file,
            FilePath::from("mymod/sub.ray"),
            ModulePath::from("mymod::sub"),
        );
        // utils imports "sub" — should resolve to child (mymod::utils::sub), not sibling (mymod::sub)
        FileSource::new(&db, utils_file, "import sub".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("mymod/utils/mod.ray"),
            ModulePath::from("mymod::utils"),
        );

        let result = resolved_imports(&db, utils_file);

        assert_eq!(result.len(), 1);
        let sub_result = result.get("sub").unwrap();
        assert!(sub_result.is_ok());
        let resolved = sub_result.as_ref().unwrap();
        assert_eq!(
            resolved.module_path.to_string(),
            "mymod::utils::sub",
            "child resolution should take priority over sibling"
        );
    }

    // =========================================================================
    // Tests for import_export_targets
    // =========================================================================

    #[test]
    fn import_export_targets_namespace_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "import utils".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let targets = import_export_targets(&db, file_id);
        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 1);
        let ImportKind::Path(ref path_node) = imports[0].kind else {
            panic!("Expected Path import");
        };

        let target = targets
            .get(&path_node.id)
            .expect("path node should have a target");
        assert_eq!(
            *target,
            ImportExportTarget::Module(ModulePath::from("utils"))
        );
    }

    #[test]
    fn import_export_targets_selective_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "import utils with helper, other".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let targets = import_export_targets(&db, file_id);
        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 1);
        let ImportKind::Names(ref path_node, ref name_nodes) = imports[0].kind else {
            panic!("Expected Names import");
        };

        // Module path node maps to Module target
        let path_target = targets
            .get(&path_node.id)
            .expect("path node should have a target");
        assert_eq!(
            *path_target,
            ImportExportTarget::Module(ModulePath::from("utils"))
        );

        // Each name node maps to ModuleName target
        assert_eq!(name_nodes.len(), 2);
        let name0_target = targets
            .get(&name_nodes[0].id)
            .expect("first name node should have a target");
        assert_eq!(
            *name0_target,
            ImportExportTarget::ModuleName {
                module: ModulePath::from("utils"),
                name: "helper".to_string(),
            }
        );

        let name1_target = targets
            .get(&name_nodes[1].id)
            .expect("second name node should have a target");
        assert_eq!(
            *name1_target,
            ImportExportTarget::ModuleName {
                module: ModulePath::from("utils"),
                name: "other".to_string(),
            }
        );
    }

    #[test]
    fn import_export_targets_glob_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "import utils with *".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let targets = import_export_targets(&db, file_id);
        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 1);
        let ImportKind::Glob(ref path_node) = imports[0].kind else {
            panic!("Expected Glob import");
        };

        let target = targets
            .get(&path_node.id)
            .expect("path node should have a target");
        assert_eq!(
            *target,
            ImportExportTarget::Module(ModulePath::from("utils"))
        );
    }

    #[test]
    fn import_export_targets_unresolved_import_has_no_entry() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, file_id, "import nonexistent".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let targets = import_export_targets(&db, file_id);

        // Unresolved import should produce no targets
        assert!(
            targets.is_empty(),
            "Unresolved import should not appear in targets"
        );
    }

    #[test]
    fn import_export_targets_export_path() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        let file_id =
            workspace.add_file(FilePath::from("mymod/mod.ray"), ModulePath::from("mymod"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

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
            FilePath::from("mymod/mod.ray"),
            ModulePath::from("mymod"),
        );

        let targets = import_export_targets(&db, file_id);
        let parse_result = parse_file_raw(&db, file_id);

        assert_eq!(parse_result.ast.exports.len(), 1);
        let ExportKind::Path(ref path_node) = parse_result.ast.exports[0].kind else {
            panic!("Expected Path export");
        };

        let target = targets
            .get(&path_node.id)
            .expect("export path node should have a target");
        assert_eq!(
            *target,
            ImportExportTarget::Module(ModulePath::from("utils"))
        );
    }

    #[test]
    fn import_export_targets_export_with_names() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        let file_id =
            workspace.add_file(FilePath::from("mymod/mod.ray"), ModulePath::from("mymod"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, file_id, "export utils with helper".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("mymod/mod.ray"),
            ModulePath::from("mymod"),
        );

        let targets = import_export_targets(&db, file_id);
        let parse_result = parse_file_raw(&db, file_id);

        assert_eq!(parse_result.ast.exports.len(), 1);
        let ExportKind::Names(ref path_node, ref name_nodes) = parse_result.ast.exports[0].kind
        else {
            panic!("Expected Names export");
        };

        // Module path maps to Module target
        let path_target = targets
            .get(&path_node.id)
            .expect("export path node should have a target");
        assert_eq!(
            *path_target,
            ImportExportTarget::Module(ModulePath::from("utils"))
        );

        // Name node maps to ModuleName target
        assert_eq!(name_nodes.len(), 1);
        let name_target = targets
            .get(&name_nodes[0].id)
            .expect("export name node should have a target");
        assert_eq!(
            *name_target,
            ImportExportTarget::ModuleName {
                module: ModulePath::from("utils"),
                name: "helper".to_string(),
            }
        );
    }

    #[test]
    fn import_export_targets_no_imports_or_exports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, file_id, "fn main() {}".to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let targets = import_export_targets(&db, file_id);

        assert!(targets.is_empty(), "No imports or exports means no targets");
    }

    #[test]
    fn import_export_targets_multiple_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let utils_file =
            workspace.add_file(FilePath::from("utils/mod.ray"), ModulePath::from("utils"));
        let io_file = workspace.add_file(
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        let file_id = workspace.add_file(FilePath::from("main.ray"), ModulePath::from("main"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);

        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileMetadata::new(
            &db,
            utils_file,
            FilePath::from("utils/mod.ray"),
            ModulePath::from("utils"),
        );
        FileSource::new(&db, io_file, "fn read() {}".to_string());
        FileMetadata::new(
            &db,
            io_file,
            FilePath::from("std/io/mod.ray"),
            ModulePath::from("std::io"),
        );
        FileSource::new(
            &db,
            file_id,
            "import utils\nimport std::io with read".to_string(),
        );
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("main.ray"),
            ModulePath::from("main"),
        );

        let targets = import_export_targets(&db, file_id);
        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 2);

        // First import: `import utils` (Path)
        let ImportKind::Path(ref path_node0) = imports[0].kind else {
            panic!("Expected Path import for utils");
        };
        assert_eq!(
            *targets.get(&path_node0.id).unwrap(),
            ImportExportTarget::Module(ModulePath::from("utils"))
        );

        // Second import: `import std::io with read` (Names)
        let ImportKind::Names(ref path_node1, ref name_nodes1) = imports[1].kind else {
            panic!("Expected Names import for std::io");
        };
        assert_eq!(
            *targets.get(&path_node1.id).unwrap(),
            ImportExportTarget::Module(ModulePath::from("std::io"))
        );
        assert_eq!(
            *targets.get(&name_nodes1[0].id).unwrap(),
            ImportExportTarget::ModuleName {
                module: ModulePath::from("std::io"),
                name: "read".to_string(),
            }
        );
    }
}
