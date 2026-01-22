//! Import extraction and resolution queries for the incremental compiler.

use std::collections::HashMap;

use ray_core::ast::{Import, ImportKind};
use ray_query_macros::query;
use ray_shared::{file_id::FileId, pathlib::ModulePath};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{libraries::LoadedLibraries, parse::parse_file, workspace::WorkspaceSnapshot},
    query::{Database, Query},
};

/// Extract all import statements from a file.
#[query]
pub fn file_imports(db: &Database, file_id: FileId) -> Vec<Import> {
    let parse_result = parse_file(db, file_id);
    parse_result.ast.imports
}

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

/// A resolved import with its module path and optional selective names.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedImport {
    /// The resolved module path.
    pub module_path: ModulePath,
    /// If Some, only these names are brought into scope (selective import).
    /// If None, all exports are brought into scope (glob import).
    pub names: Option<Vec<String>>,
}

/// Resolve all imports in a file to their target module paths.
///
/// Returns a map from import alias (or module name if no alias) to the resolved
/// import info or an error. Each import produces one entry in the result.
///
/// For `import std::io`, the key is "io" (the last component), names is None (glob).
/// For `import std::io with File, Read`, the key is "io", names is Some(["File", "Read"]).
#[query]
pub fn resolved_imports(
    db: &Database,
    file_id: FileId,
) -> HashMap<String, Result<ResolvedImport, ImportError>> {
    let imports = file_imports(db, file_id);
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let libraries = db.get_input::<LoadedLibraries>(());

    resolve_imports(&imports, &workspace, &libraries)
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
                let path = &path_node.value;
                let alias = path.to_short_name();
                let module_path = ModulePath::from(path);
                let resolution = resolve_module_path(&module_path, workspace, libraries)
                    .map(|mp| ResolvedImport { module_path: mp, names: None });
                result.insert(alias, resolution);
            }
            ImportKind::Names(path_node, names) => {
                // For `import foo::bar with X, Y`, we resolve foo::bar as the module
                // and record the specific names to bring into scope
                let path = &path_node.value;
                let alias = path.to_short_name();
                let module_path = ModulePath::from(path);
                let name_strings: Vec<String> = names.iter().map(|n| n.to_string()).collect();
                let resolution = resolve_module_path(&module_path, workspace, libraries)
                    .map(|mp| ResolvedImport { module_path: mp, names: Some(name_strings) });
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
    // Check if the module exists in the workspace (convert to Path for lookup)
    if workspace.module_info(&module_path.to_path()).is_some() {
        return Ok(module_path.clone());
    }

    // Check if the module exists in loaded libraries
    if libraries.has_module(&module_path.to_path()) {
        return Ok(module_path.clone());
    }

    // Module not found
    Err(ImportError::UnknownModule(module_path.to_string()))
}

#[cfg(test)]
mod tests {
    use ray_shared::pathlib::FilePath;

    use crate::{
        queries::{
            imports::{file_imports, resolved_imports, ImportError},
            libraries::LoadedLibraries,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
    }

    #[test]
    fn file_imports_returns_empty_for_no_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let imports = file_imports(&db, file_id);

        assert!(imports.is_empty());
    }

    #[test]
    fn file_imports_extracts_path_import() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, "import std::io\nfn main() {}".to_string());

        let imports = file_imports(&db, file_id);

        assert_eq!(imports.len(), 1);
    }

    #[test]
    fn file_imports_extracts_multiple_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
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
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
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
    fn resolved_imports_returns_empty_for_no_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let result = resolved_imports(&db, file_id);

        assert!(result.is_empty());
    }

    #[test]
    fn resolved_imports_resolves_existing_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Create a module "utils" with a file
        let utils_file = workspace.add_file(
            FilePath::from("utils/mod.ray"),
            ray_shared::pathlib::Path::from("utils"),
        );
        // Create the main file that imports utils
        let file_id = workspace.add_file(
            FilePath::from("main.ray"),
            ray_shared::pathlib::Path::from("main"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, utils_file, "fn helper() {}".to_string());
        FileSource::new(&db, file_id, "import utils".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let utils_result = result.get("utils").expect("should have utils import");
        assert!(utils_result.is_ok());
        let resolved = utils_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "utils");
        assert!(resolved.names.is_none()); // glob import
    }

    #[test]
    fn resolved_imports_returns_error_for_unknown_module() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(
            FilePath::from("test.ray"),
            ray_shared::pathlib::Path::from("test"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
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
            ray_shared::pathlib::Path::from("std::io"),
        );
        let file_id = workspace.add_file(
            FilePath::from("main.ray"),
            ray_shared::pathlib::Path::from("main"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, io_file, "fn read() {}".to_string());
        FileSource::new(&db, file_id, "import std::io".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        // The alias is the last component "io"
        let io_result = result.get("io").expect("should have io import");
        assert!(io_result.is_ok());
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "std::io");
        assert!(resolved.names.is_none()); // glob import
    }

    #[test]
    fn resolved_imports_handles_named_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let io_file = workspace.add_file(
            FilePath::from("std/io/mod.ray"),
            ray_shared::pathlib::Path::from("std::io"),
        );
        let file_id = workspace.add_file(
            FilePath::from("main.ray"),
            ray_shared::pathlib::Path::from("main"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, io_file, "fn read() {}".to_string());
        FileSource::new(&db, file_id, "import std::io with File, Read".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        // The module path is resolved, named imports are just names to bring into scope
        let io_result = result.get("io").expect("should have io import");
        assert!(io_result.is_ok());
        let resolved = io_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "std::io");
        assert_eq!(resolved.names, Some(vec!["File".to_string(), "Read".to_string()]));
    }

    #[test]
    fn resolved_imports_handles_multiple_imports() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let io_file = workspace.add_file(
            FilePath::from("std/io/mod.ray"),
            ray_shared::pathlib::Path::from("std::io"),
        );
        let collections_file = workspace.add_file(
            FilePath::from("std/collections/mod.ray"),
            ray_shared::pathlib::Path::from("std::collections"),
        );
        let file_id = workspace.add_file(
            FilePath::from("main.ray"),
            ray_shared::pathlib::Path::from("main"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
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
        let file_id = workspace.add_file(
            FilePath::from("main.ray"),
            ray_shared::pathlib::Path::from("main"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core::io module
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = crate::queries::libraries::LibraryData::default();
        core_lib.modules.push(ray_shared::pathlib::Path::from("core::io"));
        libraries.add(ray_shared::pathlib::Path::from("core"), core_lib);
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
        let file_id = workspace.add_file(
            FilePath::from("main.ray"),
            ray_shared::pathlib::Path::from("main"),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with core as the root
        let mut libraries = LoadedLibraries::default();
        let core_lib = crate::queries::libraries::LibraryData::default();
        libraries.add(ray_shared::pathlib::Path::from("core"), core_lib);
        LoadedLibraries::new(&db, (), libraries.libraries);

        FileSource::new(&db, file_id, "import core".to_string());

        let result = resolved_imports(&db, file_id);

        assert_eq!(result.len(), 1);
        let core_result = result.get("core").expect("should have core import");
        assert!(core_result.is_ok(), "Library root should resolve");
        let resolved = core_result.as_ref().unwrap();
        assert_eq!(resolved.module_path.to_string(), "core");
    }
}
