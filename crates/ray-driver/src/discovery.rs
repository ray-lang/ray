//! Workspace discovery: finds source files and libraries by following imports.
//!
//! This module implements the `build_snapshot` algorithm from the incremental compilation spec.
//! Discovery is NOT a query - it runs before queries to populate inputs.

use std::collections::{HashMap, HashSet, VecDeque};

/// Options for workspace discovery.
#[derive(Debug, Clone, Default)]
pub struct DiscoveryOptions {
    /// If true, don't inject implicit core imports.
    pub no_core: bool,
    /// If true, discover ALL submodules (for library builds).
    /// When false, only discover modules reachable via imports.
    pub build_lib: bool,
    /// If true, also load the `testing` library for test mode.
    pub test_mode: bool,
}

use ray_core::{
    ast::{Export, ExportKind, Import, ImportKind},
    errors::{RayError, RayErrorKind},
    sema::root,
};
use ray_frontend::queries::{
    libraries::{LoadedLibraries, load_library},
    parse::parse_file,
    workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
};
use ray_shared::{
    pathlib::{FilePath, ModulePath},
    ty::SchemaVarAllocator,
};

use ray_frontend::query::Database;

/// Result of resolving an import path.
#[derive(Debug)]
pub enum ImportResolution {
    /// Source module: returns module path AND all files in that module.
    SourceModule(ModulePath, Vec<FilePath>),
    /// Precompiled library: returns module path and .raylib file path.
    Library(ModulePath, FilePath),
    /// Module not found.
    NotFound,
}

/// Discover all source files and libraries reachable from an entry point.
///
/// This is the main discovery function that builds `WorkspaceSnapshot` and
/// `LoadedLibraries` by following imports from the entry file.
///
/// # Arguments
/// * `db` - The query database (used for parsing files)
/// * `entry_path` - Path to the entry point file or directory
/// * `search_paths` - Library search directories (from RayPaths + BuildOptions)
/// * `options` - Discovery options (no_core, build_lib)
/// * `overlays` - Optional file content overlays (for LSP and tests)
///
/// # Returns
/// Tuple of (WorkspaceSnapshot, LoadedLibraries) ready to be set as inputs.
pub fn discover_workspace(
    db: &Database,
    entry_path: &FilePath,
    search_paths: Vec<FilePath>,
    options: DiscoveryOptions,
    overlays: Option<&HashMap<FilePath, String>>,
) -> Result<(WorkspaceSnapshot, LoadedLibraries), RayError> {
    // Resolve entry: could be a .ray file or a directory
    let (entry_file, entry_dir) = resolve_entry_path(entry_path)?;

    let mut snapshot = WorkspaceSnapshot::new();
    snapshot.search_paths = search_paths.clone();

    let mut loaded_libs = LoadedLibraries::default();
    let mut schema_var_allocator = SchemaVarAllocator::new();

    let mut pending: VecDeque<FilePath> = VecDeque::new();
    let mut seen: HashSet<FilePath> = HashSet::new();

    let entry_module = discover_module_for_file(&entry_file);
    pending.push_back(entry_file.clone());

    // For library builds, also discover all submodules in the entry directory
    if options.build_lib {
        if let Some(dir) = &entry_dir {
            discover_all_submodules(dir, &entry_module, &mut pending);
        }
    }

    // Track if we've injected core imports
    let mut core_injected = false;

    while let Some(file_path) = pending.pop_front() {
        // Canonicalize to avoid duplicate processing
        let file_path = file_path.canonicalize().unwrap_or(file_path);

        if !seen.insert(file_path.clone()) {
            continue;
        }

        // Determine module path for this file
        let module_path = discover_module_for_file(&file_path);

        // Add file to snapshot
        let file_id = snapshot.add_file(file_path.clone(), module_path.clone());

        // Set entry if this is the first file
        if snapshot.entry.is_none() {
            snapshot.entry = Some(file_id);
        }

        // Set file source (from overlay if available, otherwise from disk)
        let content = if let Some(overlay) = overlays.and_then(|o| o.get(&file_path)) {
            overlay.clone()
        } else {
            std::fs::read_to_string(&file_path)?
        };
        FileSource::new(db, file_id, content);

        // Set per-file metadata so parse_file can depend on stable file identity
        // without depending on the volatile WorkspaceSnapshot (which is set
        // incrementally during discovery and would produce unstable fingerprints).
        FileMetadata::new(db, file_id, file_path.clone(), module_path.clone());

        // We need to set the workspace snapshot before parsing so the query works
        db.set_input::<WorkspaceSnapshot>((), snapshot.clone());

        // Parse to get imports (uses parse_file query)
        let parse_result = parse_file(db, file_id);

        // Process imports
        for import in &parse_result.ast.imports {
            if let Some(import_module_path) = extract_module_path(import) {
                match resolve_import(&import_module_path, &file_path, &search_paths) {
                    ImportResolution::SourceModule(_mod_path, files) => {
                        // Add ALL files in the imported module (per spec)
                        for file in files {
                            pending.push_back(file);
                        }
                    }
                    ImportResolution::Library(lib_mod_path, lib_file_path) => {
                        if !loaded_libs.libraries.contains_key(&lib_mod_path) {
                            let lib_data = load_library(&lib_file_path, &mut schema_var_allocator)?;
                            loaded_libs.add_from_file(lib_mod_path, lib_file_path, lib_data);
                        }
                    }
                    ImportResolution::NotFound => {
                        // Will be reported as error during resolved_imports query
                        log::debug!(
                            "Import not found during discovery: {} (from {})",
                            import_module_path,
                            file_path
                        );
                    }
                }
            }
        }

        // Process exports — discover referenced modules just like imports
        for export in &parse_result.ast.exports {
            if let Some(export_module_path) = extract_export_module_path(export) {
                match resolve_import(&export_module_path, &file_path, &search_paths) {
                    ImportResolution::SourceModule(_mod_path, files) => {
                        for file in files {
                            pending.push_back(file);
                        }
                    }
                    ImportResolution::Library(lib_mod_path, lib_file_path) => {
                        if !loaded_libs.libraries.contains_key(&lib_mod_path) {
                            let lib_data = load_library(&lib_file_path, &mut schema_var_allocator)?;
                            loaded_libs.add_from_file(lib_mod_path, lib_file_path, lib_data);
                        }
                    }
                    ImportResolution::NotFound => {
                        log::debug!(
                            "Export target not found during discovery: {} (from {})",
                            export_module_path,
                            file_path
                        );
                    }
                }
            }
        }

        // Load core libraries (only once, not for core files themselves)
        // The query system will later inject the implicit imports.
        if !options.no_core && !core_injected && !module_path.starts_with("core") {
            core_injected = true;
            ensure_core_libraries_loaded(
                &mut loaded_libs,
                &search_paths,
                &mut schema_var_allocator,
            );

            // Also load the testing library if available
            ensure_testing_library_loaded(
                &mut loaded_libs,
                &search_paths,
                &mut schema_var_allocator,
            );
        }
    }

    Ok((snapshot, loaded_libs))
}

/// Determine the module path for a file based on its filesystem location.
///
/// Each file is its own module. Facade files (`mod.ray` or `<dirname>.ray`)
/// represent the directory module; all other files get a child module path.
///
/// Examples:
/// - `foo.ray` (not in module dir) → `foo`
/// - `mymod/mod.ray` → `mymod`           (facade)
/// - `mymod/helpers.ray` → `mymod::helpers` (non-facade)
/// - `mymod/sub/mod.ray` → `mymod::sub`  (facade)
/// - `mymod/sub/util.ray` → `mymod::sub::util` (non-facade)
pub fn discover_module_for_file(filepath: &FilePath) -> ModulePath {
    // Single-file module: if this is a file and its directory is not a dir-module,
    // treat the file itself as the root module and use its stem.
    if !filepath.is_dir() && !root::is_dir_module(&filepath.dir()) {
        return ModulePath::from(filepath.file_stem().as_str());
    }

    // Start from the directory that contains this module
    let module_dir = filepath.dir();

    // Walk upward capturing a contiguous chain of module entry directories.
    // A "module directory" is one that contains `mod.ray` or `<basename>.ray`.
    let mut chain: Vec<FilePath> = Vec::new();
    let mut curr = module_dir.clone();
    loop {
        if !root::is_dir_module(&curr) {
            break;
        }
        chain.push(curr.clone());
        match curr.parent_dir() {
            Some(parent) if root::is_dir_module(&parent) => {
                curr = parent;
            }
            _ => break,
        }
    }

    // If we didn't find any entry dirs, fall back to a single segment: the immediate directory name.
    if chain.is_empty() {
        return ModulePath::from(module_dir.file_name().as_str());
    }

    // Build the directory module path from the TOPMOST contiguous entry dir down to `module_dir`.
    let parts: Vec<String> = chain.iter().rev().map(|d| d.file_name()).collect();
    let dir_module_path = ModulePath::new(parts);

    // File = Module: non-facade files get their own child module path.
    // A facade file is `mod.ray` or `<dirname>.ray`.
    if !is_facade_file(filepath) {
        let mut segments = dir_module_path.segments().to_vec();
        segments.push(filepath.file_stem());
        return ModulePath::new(segments);
    }

    dir_module_path
}

/// Returns true if the file is a facade file for its directory module.
///
/// Facade files are `mod.ray` or `<dirname>.ray` — they represent the
/// directory module itself rather than being a child module.
fn is_facade_file(filepath: &FilePath) -> bool {
    let filename = filepath.file_name();
    if filename == "mod.ray" {
        return true;
    }
    let dir = filepath.dir();
    let dir_name = dir.file_name();
    filename == format!("{}.ray", dir_name)
}

/// Resolve an import path to either a source module or a library.
///
/// Search order:
/// 1. Relative to current module directory
/// 2. In search paths (libraries first, then source)
pub fn resolve_import(
    import_path: &ModulePath,
    from_file: &FilePath,
    search_paths: &[FilePath],
) -> ImportResolution {
    // Current directory for relative resolution
    let curr_dir = from_file.dir();

    // 1. Try relative resolution from current directory
    if let Some(result) = try_resolve_in_dir(import_path, &curr_dir) {
        return result;
    }

    // 2. Try resolution in search paths
    for search_path in search_paths {
        // Check for .raylib file first: {search_path}/{module}#.raylib
        let lib_file = library_path_for_module(search_path, import_path);
        if lib_file.exists() {
            return ImportResolution::Library(import_path.clone(), lib_file);
        }

        // Check for source directory
        if let Some(result) = try_resolve_in_dir(import_path, search_path) {
            return result;
        }
    }

    ImportResolution::NotFound
}

/// Try to resolve a module path within a base directory.
///
/// In the file=module model, importing a directory module discovers only
/// the facade file (`mod.ray` or `<dirname>.ray`). The facade's own
/// imports and exports will pull in sibling files as needed.
fn try_resolve_in_dir(import_path: &ModulePath, base_dir: &FilePath) -> Option<ImportResolution> {
    // Convert module path to file path: foo::bar -> foo/bar
    let relative_path = import_path.to_path().to_filepath();
    let target_dir = base_dir / &relative_path;

    // Check for single-file module: foo/bar.ray
    let single_file = target_dir.with_extension("ray");
    if single_file.exists() && !single_file.is_dir() {
        return Some(ImportResolution::SourceModule(
            import_path.clone(),
            vec![single_file],
        ));
    }

    // Check for directory module: only return the facade file
    if target_dir.is_dir() && root::is_dir_module(&target_dir) {
        if let Some(facade) = find_facade_file(&target_dir) {
            return Some(ImportResolution::SourceModule(
                import_path.clone(),
                vec![facade],
            ));
        }
    }

    None
}

/// Find the facade file for a directory module.
///
/// The facade file is `mod.ray` or `<dirname>.ray`. Returns `None` if
/// neither exists (shouldn't happen for a valid dir-module).
fn find_facade_file(dir: &FilePath) -> Option<FilePath> {
    let mod_file = dir / "mod.ray";
    if mod_file.exists() {
        return Some(mod_file);
    }
    let name = dir.file_name();
    let named_file = dir / &format!("{}.ray", name);
    if named_file.exists() {
        return Some(named_file);
    }
    None
}

/// Construct the library file path for a module.
///
/// Library files are named with `#` as separator between segments:
/// - `core` → `core.raylib`
/// - `core::io` → `core#io.raylib`
fn library_path_for_module(search_path: &FilePath, module_path: &ModulePath) -> FilePath {
    // Convert module path segments to #-separated filename, then add .raylib extension
    let segments = module_path.segments();
    let lib_name = segments.join("#");
    (search_path / &lib_name).with_extension("raylib")
}

/// Resolve an entry path to the entry file and optional entry directory.
///
/// - If entry_path is a `.ray` file, returns (file, None) or (file, Some(dir)) if in a module dir.
/// - If entry_path is a directory, finds mod.ray or <name>.ray and returns (file, Some(dir)).
fn resolve_entry_path(entry_path: &FilePath) -> Result<(FilePath, Option<FilePath>), RayError> {
    if entry_path.is_dir() {
        // Directory entry: find the module entry file
        let base = entry_path.file_name();
        let mod_file = entry_path / "mod.ray";
        let named_file = entry_path / format!("{}.ray", base);

        let entry_file = if mod_file.exists() {
            mod_file
        } else if named_file.exists() {
            named_file
        } else {
            return Err(RayError {
                msg: format!(
                    "No module entry file found. Expected {}/mod.ray or {}/{}.ray",
                    entry_path, entry_path, base
                ),
                src: vec![],
                kind: RayErrorKind::Compile,
                context: None,
            });
        };

        Ok((entry_file, Some(entry_path.clone())))
    } else if entry_path.has_extension("ray") {
        // File entry: check if it's in a module directory
        let dir = entry_path.dir();
        let entry_dir = if root::is_dir_module(&dir) {
            Some(dir)
        } else {
            None
        };
        Ok((entry_path.clone(), entry_dir))
    } else {
        Err(RayError {
            msg: format!("entry must be a .ray file or directory: {}", entry_path),
            src: vec![],
            kind: RayErrorKind::Compile,
            context: None,
        })
    }
}

/// Recursively discover all submodule files in a directory (for library builds).
///
/// Unlike import-based discovery, this walks the entire directory tree to find
/// ALL modules that should be included in the library.
fn discover_all_submodules(
    dir: &FilePath,
    parent_module: &ModulePath,
    pending: &mut VecDeque<FilePath>,
) {
    let entries = match dir.read_dir() {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = FilePath::from(entry.path());

        if path.is_dir() && root::is_dir_module(&path) {
            // This is a submodule directory — recurse into it
            let submodule_name = path.file_name();
            let mut segments = parent_module.segments().to_vec();
            segments.push(submodule_name);
            let submodule_path = ModulePath::new(segments);
            discover_all_submodules(&path, &submodule_path, pending);
        } else if path.has_extension("ray") {
            pending.push_back(path);
        }
    }
}

/// Extract the module path from an import statement.
fn extract_module_path(import: &Import) -> Option<ModulePath> {
    match &import.kind {
        ImportKind::Path(path_node) => Some(ModulePath::from(&path_node.value)),
        ImportKind::Names(path_node, _) => Some(ModulePath::from(&path_node.value)),
        ImportKind::Glob(path_node) => Some(ModulePath::from(&path_node.value)),
        ImportKind::CImport(_, _) => None, // C imports don't resolve to module paths
        ImportKind::Incomplete => None,    // Error recovery artifact
    }
}

/// Extract the module path from an export statement for discovery.
///
/// All export kinds reference a module path that needs to be discovered.
fn extract_export_module_path(export: &Export) -> Option<ModulePath> {
    match &export.kind {
        ExportKind::Path(path_node) => Some(ModulePath::from(&path_node.value)),
        ExportKind::Names(path_node, _) => Some(ModulePath::from(&path_node.value)),
        ExportKind::Glob(path_node) => Some(ModulePath::from(&path_node.value)),
        ExportKind::Incomplete => None, // Error recovery artifact
    }
}

/// Ensure core libraries are loaded into LoadedLibraries.
///
/// This is the discovery-time counterpart to `resolved_imports`' implicit import injection.
/// Discovery loads the library DATA; the query system later injects the IMPORTS.
fn ensure_core_libraries_loaded(
    loaded_libs: &mut LoadedLibraries,
    search_paths: &[FilePath],
    allocator: &mut SchemaVarAllocator,
) {
    // Try to load core library
    let core_path = ModulePath::from("core");
    for search_path in search_paths {
        let lib_file = library_path_for_module(search_path, &core_path);
        if lib_file.exists() {
            if !loaded_libs.libraries.contains_key(&core_path) {
                if let Ok(lib_data) = load_library(&lib_file, allocator) {
                    loaded_libs.add_from_file(core_path.clone(), lib_file, lib_data);
                }
            }
            break;
        }
    }

    // Also try core::io
    let io_path = ModulePath::from("core::io");
    for search_path in search_paths {
        let lib_file = library_path_for_module(search_path, &io_path);
        if lib_file.exists() {
            if !loaded_libs.libraries.contains_key(&io_path) {
                if let Ok(lib_data) = load_library(&lib_file, allocator) {
                    loaded_libs.add_from_file(io_path.clone(), lib_file, lib_data);
                }
            }
            break;
        }
    }
}

/// Ensure the testing library is loaded into LoadedLibraries.
///
/// Called in test mode so that `import testing with *` can resolve.
fn ensure_testing_library_loaded(
    loaded_libs: &mut LoadedLibraries,
    search_paths: &[FilePath],
    allocator: &mut SchemaVarAllocator,
) {
    let testing_path = ModulePath::from("testing");
    for search_path in search_paths {
        let lib_file = library_path_for_module(search_path, &testing_path);
        if lib_file.exists() {
            if !loaded_libs.libraries.contains_key(&testing_path) {
                if let Ok(lib_data) = load_library(&lib_file, allocator) {
                    loaded_libs.add_from_file(testing_path.clone(), lib_file, lib_data);
                }
            }
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;
    use std::fs;

    use ray_shared::pathlib::{FilePath, ModulePath};
    use tempfile::tempdir;

    use crate::discovery::{
        ImportResolution, discover_all_submodules, discover_module_for_file,
        library_path_for_module, resolve_entry_path, resolve_import,
    };

    #[test]
    fn test_library_path_for_module() {
        let search = FilePath::from("/lib");

        let core = ModulePath::from("core");
        assert_eq!(
            library_path_for_module(&search, &core),
            FilePath::from("/lib/core.raylib")
        );

        let core_io = ModulePath::from("core::io");
        assert_eq!(
            library_path_for_module(&search, &core_io),
            FilePath::from("/lib/core#io.raylib")
        );
    }

    #[test]
    fn discover_module_for_single_file() {
        // Single file not in a module directory should use its stem
        let dir = tempdir().unwrap();
        let file = FilePath::from(dir.path().join("foo.ray"));
        fs::write(&file, "").unwrap();

        let module_path = discover_module_for_file(&file);
        assert_eq!(module_path, ModulePath::from("foo"));
    }

    #[test]
    fn discover_module_for_facade_file() {
        // Facade file (mod.ray) should use directory name
        let dir = tempdir().unwrap();
        let module_dir = dir.path().join("mymod");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mod.ray"), "").unwrap();
        fs::write(module_dir.join("helper.ray"), "").unwrap();

        let facade = FilePath::from(module_dir.join("mod.ray"));
        assert_eq!(discover_module_for_file(&facade), ModulePath::from("mymod"));
    }

    #[test]
    fn discover_module_for_non_facade_file() {
        // Non-facade file gets its own child module path
        let dir = tempdir().unwrap();
        let module_dir = dir.path().join("mymod");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mod.ray"), "").unwrap();
        fs::write(module_dir.join("helper.ray"), "").unwrap();

        let file = FilePath::from(module_dir.join("helper.ray"));
        let module_path = discover_module_for_file(&file);
        assert_eq!(module_path, ModulePath::from("mymod::helper"));
    }

    #[test]
    fn discover_module_for_named_facade_file() {
        // Named facade file (<dirname>.ray) should use directory name
        let dir = tempdir().unwrap();
        let module_dir = dir.path().join("mymod");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mymod.ray"), "").unwrap();

        let facade = FilePath::from(module_dir.join("mymod.ray"));
        assert_eq!(discover_module_for_file(&facade), ModulePath::from("mymod"));
    }

    #[test]
    fn discover_module_for_nested_modules() {
        // Nested module directories should produce nested module paths
        let dir = tempdir().unwrap();
        let outer = dir.path().join("outer");
        let inner = outer.join("inner");
        fs::create_dir_all(&inner).unwrap();
        fs::write(outer.join("mod.ray"), "").unwrap();
        fs::write(inner.join("mod.ray"), "").unwrap();

        let file = FilePath::from(inner.join("mod.ray"));
        let module_path = discover_module_for_file(&file);
        assert_eq!(module_path, ModulePath::from("outer::inner"));
    }

    #[test]
    fn resolve_import_finds_single_file_module() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create a single-file module: foo.ray
        fs::write(root.join("foo.ray"), "").unwrap();

        // resolve_import only uses from_file's directory, not its contents
        let from_file = FilePath::from(root.join("main.ray"));

        let result = resolve_import(&ModulePath::from("foo"), &from_file, &[]);

        match result {
            ImportResolution::SourceModule(path, files) => {
                assert_eq!(path, ModulePath::from("foo"));
                assert_eq!(files.len(), 1);
                assert!(files[0].file_name() == "foo.ray");
            }
            other => panic!("expected SourceModule, got {:?}", other),
        }
    }

    #[test]
    fn resolve_import_finds_directory_module_facade_only() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create a directory module: bar/mod.ray, bar/helper.ray
        let bar_dir = root.join("bar");
        fs::create_dir(&bar_dir).unwrap();
        fs::write(bar_dir.join("mod.ray"), "").unwrap();
        fs::write(bar_dir.join("helper.ray"), "").unwrap();

        // resolve_import only uses from_file's directory, not its contents
        let from_file = FilePath::from(root.join("main.ray"));

        let result = resolve_import(&ModulePath::from("bar"), &from_file, &[]);

        match result {
            ImportResolution::SourceModule(path, files) => {
                assert_eq!(path, ModulePath::from("bar"));
                // In file=module model, only the facade file is returned
                assert_eq!(files.len(), 1);
                assert_eq!(files[0].file_name(), "mod.ray");
            }
            other => panic!("expected SourceModule, got {:?}", other),
        }
    }

    #[test]
    fn resolve_import_finds_library_in_search_path() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create a library file in a search path
        let lib_dir = root.join("libs");
        fs::create_dir(&lib_dir).unwrap();
        fs::write(lib_dir.join("mylib.raylib"), "").unwrap();

        // resolve_import only uses from_file's directory, not its contents
        let from_file = FilePath::from(root.join("main.ray"));

        let search_paths = vec![FilePath::from(&lib_dir)];
        let result = resolve_import(&ModulePath::from("mylib"), &from_file, &search_paths);

        match result {
            ImportResolution::Library(path, lib_file) => {
                assert_eq!(path, ModulePath::from("mylib"));
                assert!(lib_file.file_name() == "mylib.raylib");
            }
            other => panic!("expected Library, got {:?}", other),
        }
    }

    #[test]
    fn resolve_import_returns_not_found_for_missing_module() {
        let dir = tempdir().unwrap();
        // resolve_import only uses from_file's directory
        let from_file = FilePath::from(dir.path().join("main.ray"));

        let result = resolve_import(&ModulePath::from("nonexistent"), &from_file, &[]);

        assert!(matches!(result, ImportResolution::NotFound));
    }

    #[test]
    fn resolve_import_prefers_library_over_source_in_search_path() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create both a library and source in the search path
        let search = root.join("search");
        fs::create_dir(&search).unwrap();
        fs::write(search.join("conflict.raylib"), "").unwrap();
        let conflict_dir = search.join("conflict");
        fs::create_dir(&conflict_dir).unwrap();
        fs::write(conflict_dir.join("mod.ray"), "").unwrap();

        // resolve_import only uses from_file's directory
        let from_file = FilePath::from(root.join("main.ray"));

        let search_paths = vec![FilePath::from(&search)];
        let result = resolve_import(&ModulePath::from("conflict"), &from_file, &search_paths);

        // Library should be preferred
        assert!(
            matches!(result, ImportResolution::Library(_, _)),
            "expected Library to be preferred over source, got {:?}",
            result
        );
    }

    #[test]
    fn discover_all_submodules_finds_nested_modules() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create a module structure:
        // mylib/
        //   mod.ray
        //   helper.ray
        //   sub/
        //     mod.ray
        //     util.ray
        //     nested/
        //       mod.ray
        let lib_dir = root.join("mylib");
        fs::create_dir_all(&lib_dir).unwrap();
        fs::write(lib_dir.join("mod.ray"), "").unwrap();
        fs::write(lib_dir.join("helper.ray"), "").unwrap();

        let sub_dir = lib_dir.join("sub");
        fs::create_dir(&sub_dir).unwrap();
        fs::write(sub_dir.join("mod.ray"), "").unwrap();
        fs::write(sub_dir.join("util.ray"), "").unwrap();

        let nested_dir = sub_dir.join("nested");
        fs::create_dir(&nested_dir).unwrap();
        fs::write(nested_dir.join("mod.ray"), "").unwrap();

        // Discover all submodules from the root
        let mut pending = VecDeque::new();
        let root_module = ModulePath::from("mylib");
        discover_all_submodules(&FilePath::from(&lib_dir), &root_module, &mut pending);

        // Should find all 5 files: mod.ray, helper.ray, sub/mod.ray, sub/util.ray, sub/nested/mod.ray
        assert_eq!(pending.len(), 5);

        let file_names: Vec<String> = pending.iter().map(|p| p.file_name()).collect();
        assert!(file_names.iter().filter(|n| *n == "mod.ray").count() == 3);
        assert!(file_names.iter().any(|n| n == "helper.ray"));
        assert!(file_names.iter().any(|n| n == "util.ray"));
    }

    #[test]
    fn resolve_entry_path_handles_file() {
        let dir = tempdir().unwrap();
        let file = FilePath::from(dir.path().join("main.ray"));
        fs::write(&file, "").unwrap();

        let (entry_file, entry_dir) = resolve_entry_path(&file).unwrap();

        assert_eq!(entry_file, file);
        // Not in a module directory, so entry_dir should be None
        assert!(entry_dir.is_none());
    }

    #[test]
    fn resolve_entry_path_handles_directory_with_mod_ray() {
        let dir = tempdir().unwrap();
        let module_dir = FilePath::from(dir.path().join("mymod"));
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mod.ray"), "").unwrap();

        let (entry_file, entry_dir) = resolve_entry_path(&module_dir).unwrap();

        assert_eq!(entry_file.file_name(), "mod.ray");
        assert_eq!(entry_dir, Some(module_dir));
    }

    #[test]
    fn resolve_entry_path_handles_directory_with_named_file() {
        let dir = tempdir().unwrap();
        let module_dir = FilePath::from(dir.path().join("mymod"));
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mymod.ray"), "").unwrap();

        let (entry_file, entry_dir) = resolve_entry_path(&module_dir).unwrap();

        assert_eq!(entry_file.file_name(), "mymod.ray");
        assert_eq!(entry_dir, Some(module_dir));
    }

    #[test]
    fn resolve_entry_path_errors_for_invalid_directory() {
        let dir = tempdir().unwrap();
        let module_dir = FilePath::from(dir.path().join("empty"));
        fs::create_dir(&module_dir).unwrap();
        // No mod.ray or empty.ray

        let result = resolve_entry_path(&module_dir);
        assert!(result.is_err());
    }

    // =========================================================================
    // File = Module tests
    // =========================================================================

    #[test]
    fn discover_module_for_nested_non_facade() {
        // Non-facade file in nested module gets full path
        let dir = tempdir().unwrap();
        let outer = dir.path().join("outer");
        let inner = outer.join("inner");
        fs::create_dir_all(&inner).unwrap();
        fs::write(outer.join("mod.ray"), "").unwrap();
        fs::write(inner.join("mod.ray"), "").unwrap();
        fs::write(inner.join("utils.ray"), "").unwrap();

        let file = FilePath::from(inner.join("utils.ray"));
        let module_path = discover_module_for_file(&file);
        assert_eq!(module_path, ModulePath::from("outer::inner::utils"));
    }

    #[test]
    fn resolve_import_finds_sibling_file_as_module() {
        // Importing a sibling .ray file resolves as a single-file module
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create a directory module with facade and helper
        let mymod = root.join("mymod");
        fs::create_dir(&mymod).unwrap();
        fs::write(mymod.join("mod.ray"), "").unwrap();
        fs::write(mymod.join("helpers.ray"), "").unwrap();

        // From within mymod/, importing helpers should find helpers.ray
        let from_file = FilePath::from(mymod.join("mod.ray"));
        let result = resolve_import(&ModulePath::from("helpers"), &from_file, &[]);

        match result {
            ImportResolution::SourceModule(path, files) => {
                assert_eq!(path, ModulePath::from("helpers"));
                assert_eq!(files.len(), 1);
                assert_eq!(files[0].file_name(), "helpers.ray");
            }
            other => panic!("expected SourceModule, got {:?}", other),
        }
    }
}
