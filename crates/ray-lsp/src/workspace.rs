use std::io;
use std::path::Path;
use std::sync::Arc;

use ray_cfg::ProjectCfg;
use ray_core::sema::root;
use ray_driver::discovery::{self, DiscoveryOptions};
use ray_frontend::{
    persistence::redb_backend::RedbBackend,
    queries::{
        libraries::LoadedLibraries,
        workspace::{CompilerOptions, FileMetadata, FileSource, WorkspaceSnapshot},
    },
    query::Database,
};
use ray_shared::{
    file_id::FileId,
    pathlib::{FilePath, RayPaths},
};

/// Represents a single Ray workspace backed by an incremental Database.
///
/// Each workspace corresponds to either:
/// - A directory containing a `ray.toml` (explicit workspace), or
/// - A module root directory discovered lazily when a file is opened
///   that isn't covered by any `ray.toml` workspace.
pub(crate) struct LspWorkspace {
    /// The incremental compilation database for this workspace.
    pub db: Arc<Database>,
    /// Root directory of this workspace.
    pub root: FilePath,
    /// Project configuration from `ray.toml` (default if no `ray.toml`).
    #[allow(dead_code)]
    pub config: ProjectCfg,
    /// Entry file ID for this workspace.
    #[allow(dead_code)]
    pub entry_file: FileId,
}

impl LspWorkspace {
    /// Apply a document overlay (unsaved changes) for a file.
    ///
    /// Updates the `FileSource` input, which increments the database revision
    /// and invalidates any queries that depend on this file's contents.
    pub fn apply_overlay(&self, file_id: FileId, content: String) {
        self.db
            .set_input::<FileSource>(file_id, FileSource(content));
    }

    /// Get the `FileId` for a file path within this workspace.
    pub fn file_id(&self, path: &FilePath) -> Option<FileId> {
        let snapshot = self.db.get_input::<WorkspaceSnapshot>(());
        snapshot.file_id(path)
    }

    /// Add a new file to this workspace that wasn't found during discovery.
    ///
    /// Creates a `FileId`, updates the `WorkspaceSnapshot`, and sets
    /// `FileMetadata` and `FileSource` inputs. Returns the new `FileId`.
    pub fn add_file(&self, path: &FilePath, content: String) -> FileId {
        let canonical = path.canonicalize().unwrap_or_else(|_| path.clone());
        let module_path = discovery::discover_module_for_file(&canonical);

        let mut snapshot = self.db.get_input::<WorkspaceSnapshot>(());
        let file_id = snapshot.add_file(canonical.clone(), module_path.clone());
        self.db.set_input::<WorkspaceSnapshot>((), snapshot);

        FileMetadata::new(&self.db, file_id, canonical, module_path);
        self.db
            .set_input::<FileSource>(file_id, FileSource(content));

        file_id
    }

    /// Revert a file to its on-disk content, removing the editor overlay.
    ///
    /// If the file no longer exists on disk, sets `FileSource` to an empty
    /// string (the closest to "clearing" since inputs cannot be removed).
    pub fn revert_to_disk(&self, file_id: FileId) -> Result<(), io::Error> {
        let metadata = self.db.get_input::<FileMetadata>(file_id);
        let content = std::fs::read_to_string(metadata.path.as_ref()).unwrap_or_default();
        self.db
            .set_input::<FileSource>(file_id, FileSource(content));
        Ok(())
    }

    /// Flush the database persistence backend to disk.
    ///
    /// No-op if this workspace has no persistence backend (i.e., no `ray.toml`).
    pub fn flush(&self) {
        if let Err(e) = self.db.flush_persistence() {
            log::warn!("failed to flush persistence for {}: {}", self.root, e);
        }
    }
}

/// Manages multiple Ray workspaces within an IDE workspace.
///
/// On initialization, scans the IDE root for `ray.toml` files and creates
/// a workspace for each. Files opened outside any `ray.toml` workspace
/// trigger lazy creation of a workspace rooted at their module root.
pub(crate) struct WorkspaceManager {
    workspaces: Vec<LspWorkspace>,
    ray_paths: Option<RayPaths>,
    ide_root: Option<FilePath>,
}

impl WorkspaceManager {
    pub fn new() -> Self {
        Self {
            workspaces: Vec::new(),
            ray_paths: None,
            ide_root: None,
        }
    }

    /// Initialize the workspace manager for a given IDE workspace root.
    ///
    /// Scans downward from the root for `ray.toml` files and creates
    /// a workspace for each one found.
    pub fn initialize(&mut self, ide_root: &FilePath, ray_paths: RayPaths) {
        self.ide_root = Some(ide_root.clone());
        self.ray_paths = Some(ray_paths);

        let toml_paths = scan_for_ray_toml(ide_root);

        for toml_path in toml_paths {
            let workspace_root = toml_path.dir();
            let config = match ProjectCfg::read_from(toml_path.as_ref()) {
                Ok(cfg) => cfg,
                Err(e) => {
                    log::warn!("failed to parse {}: {}", toml_path, e);
                    continue;
                }
            };

            if let Err(e) = self.init_workspace(workspace_root, config) {
                log::warn!("failed to initialize workspace at {}: {}", toml_path, e);
            }
        }
    }

    /// Look up the workspace and FileId for a given file path.
    ///
    /// Combines `workspace_for_file` and `file_id` into one call, avoiding
    /// nested if-let chains in event handlers.
    pub fn lookup_file(&self, path: &FilePath) -> Option<(&LspWorkspace, FileId)> {
        let ws = self.workspace_for_file(path)?;
        let file_id = ws.file_id(path)?;
        Some((ws, file_id))
    }

    /// Find the workspace that contains the given file path.
    pub fn workspace_for_file(&self, path: &FilePath) -> Option<&LspWorkspace> {
        let canonical = path.canonicalize().unwrap_or_else(|_| path.clone());
        self.workspaces.iter().find(|ws| {
            let ws_root = ws.root.canonicalize().unwrap_or_else(|_| ws.root.clone());
            <FilePath as AsRef<Path>>::as_ref(&canonical)
                .starts_with(<FilePath as AsRef<Path>>::as_ref(&ws_root))
        })
    }

    /// Find or create the workspace for a file.
    ///
    /// If the file isn't in an existing workspace, discovers its module root
    /// and creates a new workspace for it (without persistence, since there
    /// is no `ray.toml`).
    pub fn workspace_for_file_or_create(
        &mut self,
        path: &FilePath,
    ) -> Result<&LspWorkspace, String> {
        let canonical = path.canonicalize().unwrap_or_else(|_| path.clone());

        // Check existing workspaces first
        if let Some(idx) = self.workspaces.iter().position(|ws| {
            let ws_root = ws.root.canonicalize().unwrap_or_else(|_| ws.root.clone());
            <FilePath as AsRef<Path>>::as_ref(&canonical)
                .starts_with(<FilePath as AsRef<Path>>::as_ref(&ws_root))
        }) {
            return Ok(&self.workspaces[idx]);
        }

        // Not in any known workspace. Find the module root and create a workspace.
        let workspace_root = discover_workspace_root_for_file(path);
        self.init_workspace(workspace_root, ProjectCfg::default())?;

        Ok(self.workspaces.last().unwrap())
    }

    /// Get the number of workspaces.
    pub fn workspace_count(&self) -> usize {
        self.workspaces.len()
    }

    fn init_workspace(&mut self, root: FilePath, config: ProjectCfg) -> Result<(), String> {
        let ray_paths = self.ray_paths.as_ref().ok_or("RayPaths not initialized")?;

        let search_paths = vec![ray_paths.get_lib_path()];

        // Persistence is only used for workspaces backed by a ray.toml,
        // matching CLI behavior where cache is stored at {workspace_root}/.ray/cache.redb.
        let has_ray_toml = root.join("ray.toml").exists();
        let db = if has_ray_toml {
            let cache_path = root.join(".ray").join("cache.redb");
            match RedbBackend::new(cache_path.as_ref().to_path_buf()) {
                Ok(backend) => Database::with_persistence(Box::new(backend)),
                Err(e) => {
                    log::warn!("failed to open cache at {}: {}", cache_path, e);
                    Database::new()
                }
            }
        } else {
            Database::new()
        };

        // Set compiler options before any queries run.
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: config.no_core(),
                test_mode: false,
            },
        );

        // Run discovery. LSP uses build_lib=true so that ALL files in the
        // workspace are discovered (not just those reachable via imports),
        // enabling navigation and diagnostics for every file.
        let discovery_options = DiscoveryOptions {
            no_core: config.no_core(),
            build_lib: true,
            test_mode: false,
        };

        let (workspace, loaded_libs) =
            discovery::discover_workspace(&db, &root, search_paths, discovery_options, None)
                .map_err(|e| e.msg)?;

        let entry_file = workspace
            .entry
            .ok_or_else(|| format!("no entry file in workspace: {}", root))?;

        db.set_input::<WorkspaceSnapshot>((), workspace);
        db.set_input::<LoadedLibraries>((), loaded_libs);

        self.workspaces.push(LspWorkspace {
            db: Arc::new(db),
            root,
            config,
            entry_file,
        });

        Ok(())
    }
}

/// Scan a directory tree for `ray.toml` files.
///
/// When a `ray.toml` is found, it is added to the results and recursion stops
/// for that subtree. A `ray.toml` declares ownership over its entire directory
/// tree — scanning past that boundary would create overlapping workspaces where
/// the same files belong to multiple databases. Nested workspaces are the parent
/// workspace's responsibility and will be declared as dependencies or workspace
/// members in the parent `ray.toml` once that feature is added.
fn scan_for_ray_toml(root: &FilePath) -> Vec<FilePath> {
    let mut results = Vec::new();
    scan_for_ray_toml_recursive(root, &mut results);
    results
}

fn scan_for_ray_toml_recursive(dir: &FilePath, results: &mut Vec<FilePath>) {
    if !dir.is_dir() {
        return;
    }

    let toml_path = dir.join("ray.toml");
    if toml_path.exists() {
        results.push(toml_path);
        // Stop recursing: this workspace owns its subtree.
        return;
    }

    if let Ok(entries) = dir.read_dir() {
        for entry in entries.flatten() {
            let path = FilePath::from(entry.path());
            if path.is_dir() {
                scan_for_ray_toml_recursive(&path, results);
            }
        }
    }
}

/// Find the workspace root for a file not covered by any `ray.toml`.
///
/// Walks up from the file to find the topmost contiguous module directory
/// (using `is_dir_module`). For single-file modules (file not in a module
/// directory), returns the file itself as the entry path.
fn discover_workspace_root_for_file(filepath: &FilePath) -> FilePath {
    // Single-file module: not inside a module directory.
    if !filepath.is_dir() && !root::is_dir_module(&filepath.dir()) {
        return filepath.clone();
    }

    let module_dir = filepath.dir();
    let mut topmost = module_dir.clone();
    let mut curr = module_dir;

    loop {
        if !root::is_dir_module(&curr) {
            break;
        }
        topmost = curr.clone();
        match curr.parent_dir() {
            Some(parent) if root::is_dir_module(&parent) => {
                curr = parent;
            }
            _ => break,
        }
    }

    topmost
}

#[cfg(test)]
mod tests {
    use std::fs;

    use ray_frontend::queries::workspace::{FileMetadata, FileSource};
    use ray_shared::pathlib::{FilePath, RayPaths};
    use tempfile::tempdir;

    use crate::workspace::{WorkspaceManager, discover_workspace_root_for_file, scan_for_ray_toml};

    /// Create a minimal RayPaths pointing at a temp directory.
    fn test_ray_paths(dir: &std::path::Path) -> RayPaths {
        let lib_dir = dir.join("lib");
        fs::create_dir_all(&lib_dir).unwrap();
        RayPaths::new(FilePath::from(dir.to_path_buf()))
    }

    #[test]
    fn scan_finds_ray_toml_files() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // workspace_a/ray.toml
        let ws_a = root.join("workspace_a");
        fs::create_dir(&ws_a).unwrap();
        fs::write(ws_a.join("ray.toml"), "[package]\nname = \"a\"\n").unwrap();

        // workspace_b/ray.toml
        let ws_b = root.join("workspace_b");
        fs::create_dir(&ws_b).unwrap();
        fs::write(ws_b.join("ray.toml"), "[package]\nname = \"b\"\n").unwrap();

        // No ray.toml in root
        let results = scan_for_ray_toml(&FilePath::from(root.to_path_buf()));

        assert_eq!(results.len(), 2);
        let names: Vec<String> = results.iter().map(|p| p.dir().file_name()).collect();
        assert!(names.contains(&"workspace_a".to_string()));
        assert!(names.contains(&"workspace_b".to_string()));
    }

    #[test]
    fn scan_stops_recursing_at_ray_toml() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // parent/ray.toml — owns subtree
        let parent = root.join("parent");
        fs::create_dir(&parent).unwrap();
        fs::write(parent.join("ray.toml"), "[package]\nname = \"parent\"\n").unwrap();

        // parent/child/ray.toml — should NOT be found
        let child = parent.join("child");
        fs::create_dir(&child).unwrap();
        fs::write(child.join("ray.toml"), "[package]\nname = \"child\"\n").unwrap();

        let results = scan_for_ray_toml(&FilePath::from(root.to_path_buf()));

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].dir().file_name(), "parent");
    }

    #[test]
    fn scan_empty_directory() {
        let dir = tempdir().unwrap();
        // No ray.toml anywhere
        let results = scan_for_ray_toml(&FilePath::from(dir.path().to_path_buf()));
        assert!(results.is_empty());
    }

    #[test]
    fn scan_ray_toml_at_root() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // ray.toml at the scan root itself
        fs::write(root.join("ray.toml"), "[package]\nname = \"root\"\n").unwrap();

        // Also a child workspace that should NOT be found (root owns subtree)
        let child = root.join("child");
        fs::create_dir(&child).unwrap();
        fs::write(child.join("ray.toml"), "[package]\nname = \"child\"\n").unwrap();

        let results = scan_for_ray_toml(&FilePath::from(root.to_path_buf()));

        assert_eq!(results.len(), 1);
        let found_dir = results[0].dir();
        let expected = FilePath::from(root.to_path_buf());
        assert_eq!(found_dir, expected);
    }

    #[test]
    fn workspace_root_for_single_file() {
        let dir = tempdir().unwrap();
        let file = FilePath::from(dir.path().join("standalone.ray"));
        fs::write(&file, "fn main() {}").unwrap();

        let root = discover_workspace_root_for_file(&file);
        assert_eq!(root, file);
    }

    #[test]
    fn workspace_root_for_directory_module() {
        let dir = tempdir().unwrap();
        let module_dir = dir.path().join("mymod");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mod.ray"), "").unwrap();
        fs::write(module_dir.join("helper.ray"), "").unwrap();

        let file = FilePath::from(module_dir.join("helper.ray"));
        let root = discover_workspace_root_for_file(&file);

        assert_eq!(root, FilePath::from(module_dir));
    }

    #[test]
    fn workspace_root_for_nested_module_is_topmost() {
        let dir = tempdir().unwrap();
        let outer = dir.path().join("outer");
        let inner = outer.join("inner");
        fs::create_dir_all(&inner).unwrap();
        fs::write(outer.join("mod.ray"), "").unwrap();
        fs::write(inner.join("mod.ray"), "").unwrap();

        let file = FilePath::from(inner.join("mod.ray"));
        let root = discover_workspace_root_for_file(&file);

        // Should be the topmost module dir, not the inner one.
        assert_eq!(root, FilePath::from(outer));
    }

    #[test]
    fn workspace_root_for_named_module_entry() {
        // is_dir_module recognizes <dirname>.ray as well as mod.ray
        let dir = tempdir().unwrap();
        let module_dir = dir.path().join("mymod");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mymod.ray"), "").unwrap();
        fs::write(module_dir.join("helper.ray"), "").unwrap();

        let file = FilePath::from(module_dir.join("helper.ray"));
        let root = discover_workspace_root_for_file(&file);

        assert_eq!(root, FilePath::from(module_dir));
    }

    #[test]
    fn workspace_root_for_non_module_directory() {
        // Directory has .ray files but no mod.ray or <dirname>.ray
        let dir = tempdir().unwrap();
        let non_mod = dir.path().join("stuff");
        fs::create_dir(&non_mod).unwrap();
        fs::write(non_mod.join("foo.ray"), "fn foo() {}").unwrap();

        let file = FilePath::from(non_mod.join("foo.ray"));
        let root = discover_workspace_root_for_file(&file);

        // Should return the file itself, not the directory
        assert_eq!(root, file);
    }

    #[test]
    fn workspace_root_for_three_level_nesting() {
        let dir = tempdir().unwrap();
        let outer = dir.path().join("outer");
        let middle = outer.join("middle");
        let inner = middle.join("inner");
        fs::create_dir_all(&inner).unwrap();
        fs::write(outer.join("mod.ray"), "").unwrap();
        fs::write(middle.join("mod.ray"), "").unwrap();
        fs::write(inner.join("mod.ray"), "").unwrap();

        let file = FilePath::from(inner.join("mod.ray"));
        let root = discover_workspace_root_for_file(&file);

        // Should walk all the way up to the topmost module dir
        assert_eq!(root, FilePath::from(outer));
    }

    #[test]
    fn init_workspace_with_ray_toml() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create a workspace with ray.toml
        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn hello() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        assert_eq!(manager.workspace_count(), 1);

        // The workspace should know about mod.ray
        let ws = &manager.workspaces[0];
        let mod_path = FilePath::from(ws_dir.join("mod.ray"))
            .canonicalize()
            .unwrap();
        assert!(ws.file_id(&mod_path).is_some());
    }

    #[test]
    fn apply_overlay_updates_file_source() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn original() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        let ws = &manager.workspaces[0];
        let mod_path = FilePath::from(ws_dir.join("mod.ray"))
            .canonicalize()
            .unwrap();
        let file_id = ws
            .file_id(&mod_path)
            .expect("file should exist in workspace");

        // Verify original content
        let original = ws.db.get_input::<FileSource>(file_id);
        assert_eq!(original.0, "fn original() {}");

        // Apply overlay
        ws.apply_overlay(file_id, "fn modified() {}".to_string());

        // Verify updated content
        let updated = ws.db.get_input::<FileSource>(file_id);
        assert_eq!(updated.0, "fn modified() {}");
    }

    #[test]
    fn workspace_for_file_finds_correct_workspace() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // Two workspaces
        let ws_a = root.join("ws_a");
        fs::create_dir(&ws_a).unwrap();
        fs::write(
            ws_a.join("ray.toml"),
            "[package]\nname = \"a\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_a.join("mod.ray"), "fn a() {}").unwrap();

        let ws_b = root.join("ws_b");
        fs::create_dir(&ws_b).unwrap();
        fs::write(
            ws_b.join("ray.toml"),
            "[package]\nname = \"b\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_b.join("mod.ray"), "fn b() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        assert_eq!(manager.workspace_count(), 2);

        // File in ws_a should resolve to ws_a's workspace
        let file_a = FilePath::from(ws_a.join("mod.ray"));
        let found = manager.workspace_for_file(&file_a);
        assert!(found.is_some());
        let found_root = found.unwrap().root.canonicalize().unwrap();
        let expected_root = FilePath::from(ws_a).canonicalize().unwrap();
        assert_eq!(found_root, expected_root);
    }

    #[test]
    fn lazy_workspace_creation_for_orphan_file() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // A module directory with no ray.toml
        let module_dir = root.join("orphan_mod");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mod.ray"), "fn orphan() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        // Initialize with no ray.toml files found
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);
        assert_eq!(manager.workspace_count(), 0);

        // Opening a file in the orphan module should lazily create a workspace
        let file = FilePath::from(module_dir.join("mod.ray"));
        let result = manager.workspace_for_file_or_create(&file);
        assert!(result.is_ok());

        assert_eq!(manager.workspace_count(), 1);

        // The file should be discoverable in the new workspace
        let ws = manager.workspace_for_file(&file).unwrap();
        let canonical = file.canonicalize().unwrap();
        assert!(ws.file_id(&canonical).is_some());
    }

    #[test]
    fn add_file_to_workspace() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn hello() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        let ws = &manager.workspaces[0];

        // Create a new file on disk that wasn't part of initial discovery
        let new_file = ws_dir.join("new_helper.ray");
        fs::write(&new_file, "fn helper() {}").unwrap();
        let new_path = FilePath::from(new_file).canonicalize().unwrap();

        // The file shouldn't exist in the workspace yet
        assert!(ws.file_id(&new_path).is_none());

        // Add it via add_file
        let file_id = ws.add_file(&new_path, "fn helper() {}".to_string());

        // Now the file should be discoverable
        assert_eq!(ws.file_id(&new_path), Some(file_id));

        // FileSource should be set
        let source = ws.db.get_input::<FileSource>(file_id);
        assert_eq!(source.0, "fn helper() {}");

        // FileMetadata should be set
        let metadata = ws.db.get_input::<FileMetadata>(file_id);
        assert_eq!(metadata.path, new_path);
    }

    #[test]
    fn revert_to_disk_restores_content() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn disk_version() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        let ws = &manager.workspaces[0];
        let mod_path = FilePath::from(ws_dir.join("mod.ray"))
            .canonicalize()
            .unwrap();
        let file_id = ws.file_id(&mod_path).unwrap();

        // Apply an overlay (simulating didChange)
        ws.apply_overlay(file_id, "fn editor_version() {}".to_string());
        assert_eq!(
            ws.db.get_input::<FileSource>(file_id).0,
            "fn editor_version() {}"
        );

        // Revert to disk (simulating didClose)
        ws.revert_to_disk(file_id).unwrap();
        assert_eq!(
            ws.db.get_input::<FileSource>(file_id).0,
            "fn disk_version() {}"
        );
    }

    #[test]
    fn revert_to_disk_clears_when_file_missing() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn temp() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        let ws = &manager.workspaces[0];
        let mod_path = FilePath::from(ws_dir.join("mod.ray"))
            .canonicalize()
            .unwrap();
        let file_id = ws.file_id(&mod_path).unwrap();

        // Delete the file from disk
        fs::remove_file(ws_dir.join("mod.ray")).unwrap();

        // Revert should set to empty string
        ws.revert_to_disk(file_id).unwrap();
        assert_eq!(ws.db.get_input::<FileSource>(file_id).0, "");
    }

    #[test]
    fn flush_delegates_to_persistence() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn hello() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        let ws = &manager.workspaces[0];

        // Workspace with ray.toml should have persistence.
        // flush() should not panic or error.
        assert!(ws.db.has_persistence());
        ws.flush();

        // Verify the cache file was created
        let cache_path = ws_dir.join(".ray").join("cache.redb");
        assert!(cache_path.exists());
    }

    #[test]
    fn lookup_file_returns_workspace_and_file_id() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn hello() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        let mod_path = FilePath::from(ws_dir.join("mod.ray"))
            .canonicalize()
            .unwrap();

        let result = manager.lookup_file(&mod_path);
        assert!(result.is_some(), "lookup_file should find the file");

        let (ws, file_id) = result.unwrap();
        assert_eq!(ws.file_id(&mod_path), Some(file_id));
    }

    #[test]
    fn lookup_file_returns_none_for_unknown_file() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn hello() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        // File outside any workspace
        let outside = FilePath::from(root.join("nowhere.ray"));
        assert!(manager.lookup_file(&outside).is_none());
    }

    #[test]
    fn workspace_for_file_returns_none_outside_all_workspaces() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn hello() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        // A file in a completely separate directory
        let other_dir = tempdir().unwrap();
        let outside = FilePath::from(other_dir.path().join("other.ray"));
        fs::write(&outside, "fn other() {}").unwrap();

        assert!(manager.workspace_for_file(&outside).is_none());
    }

    #[test]
    fn workspace_for_file_or_create_reuses_existing() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        let ws_dir = root.join("mylib");
        fs::create_dir(&ws_dir).unwrap();
        fs::write(
            ws_dir.join("ray.toml"),
            "[package]\nname = \"mylib\"\ntype = \"lib\"\nno_core = true\n",
        )
        .unwrap();
        fs::write(ws_dir.join("mod.ray"), "fn hello() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);
        assert_eq!(manager.workspace_count(), 1);

        // Calling workspace_for_file_or_create on a file already in a workspace
        // should return the existing workspace, not create a new one
        let mod_path = FilePath::from(ws_dir.join("mod.ray"));
        let result = manager.workspace_for_file_or_create(&mod_path);
        assert!(result.is_ok());
        assert_eq!(manager.workspace_count(), 1);
    }

    #[test]
    fn orphan_workspace_has_no_persistence() {
        let dir = tempdir().unwrap();
        let root = dir.path();

        // A module directory with no ray.toml
        let module_dir = root.join("orphan_mod");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mod.ray"), "fn orphan() {}").unwrap();

        let ray_paths = test_ray_paths(root);
        let mut manager = WorkspaceManager::new();
        manager.initialize(&FilePath::from(root.to_path_buf()), ray_paths);

        // Lazily create workspace for the orphan file
        let file = FilePath::from(module_dir.join("mod.ray"));
        let ws = manager.workspace_for_file_or_create(&file).unwrap();

        // Orphan workspace (no ray.toml) should NOT have persistence
        assert!(
            !ws.db.has_persistence(),
            "orphan workspace should not have persistence"
        );
    }
}
