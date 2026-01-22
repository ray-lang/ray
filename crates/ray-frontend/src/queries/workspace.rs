use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::io;

use ray_query_macros::input;
use ray_shared::file_id::FileId;
use ray_shared::pathlib::{FilePath, ModulePath};

use crate::query::{Database, Input};

/// Input representing the source code contents of a file.
///
/// Keyed by `FileId` so that queries can depend on individual file contents.
/// When a file's contents change, its fingerprint changes, invalidating
/// dependent queries.
#[input(key = "FileId")]
#[derive(Clone, Hash)]
pub struct FileSource(pub String);

/// Information about a single file in the workspace.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FileInfo {
    /// The file system path to this file.
    pub path: FilePath,
    /// The module path this file belongs to.
    pub module_path: ModulePath,
}

/// Information about a module in the workspace.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleInfo {
    /// The module's logical path (e.g., `foo::bar`).
    pub path: ModulePath,
    /// Files that belong to this module.
    pub files: Vec<FileId>,
    /// Whether this is the root module of a package.
    pub is_root: bool,
}

/// A snapshot of the workspace structure.
///
/// This captures the mapping between file paths, file IDs, and module paths.
/// It is computed from the file system (for CLI) or with overlays (for LSP).
/// This is a singleton input keyed by `()`.
#[derive(Clone, Debug, Default)]
pub struct WorkspaceSnapshot {
    /// Module path -> module information.
    pub modules: HashMap<ModulePath, ModuleInfo>,
    /// File ID -> file information.
    pub files: HashMap<FileId, FileInfo>,
    /// File path -> File ID (for reverse lookup).
    pub path_to_id: HashMap<FilePath, FileId>,
    /// Counter for allocating new FileIds.
    next_file_id: u32,
}

impl WorkspaceSnapshot {
    /// Create a new empty workspace snapshot.
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a new FileId for a file path.
    ///
    /// If the file path already exists, returns the existing FileId.
    pub fn get_or_create_file_id(&mut self, path: FilePath) -> FileId {
        if let Some(&id) = self.path_to_id.get(&path) {
            return id;
        }
        let id = FileId(self.next_file_id);
        self.next_file_id += 1;
        self.path_to_id.insert(path, id);
        id
    }

    /// Register a file in the workspace.
    pub fn add_file(&mut self, path: FilePath, module_path: impl Into<ModulePath>) -> FileId {
        let module_path = module_path.into();
        let id = self.get_or_create_file_id(path.clone());
        self.files.insert(
            id,
            FileInfo {
                path,
                module_path: module_path.clone(),
            },
        );

        // Add to module's file list
        let module = self
            .modules
            .entry(module_path.clone())
            .or_insert_with(|| ModuleInfo {
                path: module_path,
                files: Vec::new(),
                is_root: false,
            });
        if !module.files.contains(&id) {
            module.files.push(id);
        }

        id
    }

    /// Get a file's information by its ID.
    pub fn file_info(&self, id: FileId) -> Option<&FileInfo> {
        self.files.get(&id)
    }

    /// Get a module's information by its path.
    pub fn module_info(&self, path: &ModulePath) -> Option<&ModuleInfo> {
        self.modules.get(path)
    }

    /// Get a FileId by file path.
    pub fn file_id(&self, path: &FilePath) -> Option<FileId> {
        self.path_to_id.get(path).copied()
    }

    /// Discover workspace structure from a directory path.
    ///
    /// This walks the directory tree, finding all `.ray` files and organizing
    /// them into modules based on the directory structure.
    ///
    /// Module path rules:
    /// - A directory is a module if it contains `mod.ray` or `<dirname>.ray`
    /// - Files in a module directory belong to that module
    /// - The root directory name becomes the root module path
    pub fn from_directory(root: &FilePath) -> io::Result<Self> {
        let mut snapshot = Self::new();
        let root = root.canonicalize().unwrap_or_else(|_| root.clone());

        if root.is_dir() {
            let root_module = ModulePath::from(root.file_name().as_str());
            snapshot.discover_directory(&root, &root_module, true)?;
        } else if root.has_extension("ray") {
            // Single file: use file stem as module path
            let module_path = ModulePath::from(root.file_stem().as_str());
            snapshot.add_file(root.clone(), module_path.clone());
            if let Some(module) = snapshot.modules.get_mut(&module_path) {
                module.is_root = true;
            }
        }

        Ok(snapshot)
    }

    /// Create a new snapshot with file content overlays applied.
    ///
    /// This is used by the LSP to provide in-memory file contents that
    /// override what's on disk. The overlay maps file paths to their contents.
    ///
    /// Files in the overlay that don't exist in the snapshot are added.
    /// The snapshot structure (modules, file IDs) remains stable.
    pub fn with_overlay(&self, overlay: &HashMap<FilePath, String>) -> Self {
        let mut snapshot = self.clone();

        // Add any new files from the overlay that aren't already tracked
        for path in overlay.keys() {
            if !snapshot.path_to_id.contains_key(path) {
                // Infer module path from file path
                // For now, use the file stem as a simple heuristic
                let module_path = ModulePath::from(path.file_stem().as_str());
                snapshot.add_file(path.clone(), module_path);
            }
        }

        snapshot
    }

    /// Recursively discover files in a directory.
    fn discover_directory(
        &mut self,
        dir: &FilePath,
        module_path: &ModulePath,
        is_root: bool,
    ) -> io::Result<()> {
        // Check if this is a valid module directory
        if !is_dir_module(dir) && !is_root {
            return Ok(());
        }

        let entries = dir.read_dir()?;
        let mut subdirs = Vec::new();

        for entry in entries.flatten() {
            let path = FilePath::from(entry.path());

            if path.is_dir() {
                subdirs.push(path);
            } else if path.has_extension("ray") {
                self.add_file(path, module_path.clone());
            }
        }

        // Mark this module
        if let Some(module) = self.modules.get_mut(module_path) {
            module.is_root = is_root;
        }

        // Process subdirectories as potential submodules
        for subdir in subdirs {
            if is_dir_module(&subdir) {
                let submodule_name = subdir.file_name();
                let mut segments = module_path.segments().to_vec();
                segments.push(submodule_name);
                let submodule_path = ModulePath::new(segments);
                self.discover_directory(&subdir, &submodule_path, false)?;
            }
        }

        Ok(())
    }

    /// Get all file IDs in the workspace.
    pub fn all_file_ids(&self) -> impl Iterator<Item = FileId> + '_ {
        self.files.keys().copied()
    }

    /// Get all module paths in the workspace.
    pub fn all_module_paths(&self) -> impl Iterator<Item = &ModulePath> + '_ {
        self.modules.keys()
    }
}

/// Returns true if the directory contains a module entry file (`mod.ray` or `<basename>.ray`).
fn is_dir_module(dir: &FilePath) -> bool {
    if !dir.is_dir() {
        return false;
    }

    let entries = match dir.read_dir() {
        Ok(entries) => entries,
        Err(_) => return false,
    };

    let base = dir.file_name();
    for entry in entries.flatten() {
        let fp = FilePath::from(entry.path());
        let filename = fp.file_name();
        if filename == "mod.ray" || filename == format!("{base}.ray") {
            return true;
        }
    }

    false
}

// Implement Hash for WorkspaceSnapshot (needed for fingerprinting)
impl Hash for WorkspaceSnapshot {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash modules in sorted order for determinism
        let mut modules: Vec<_> = self.modules.iter().collect();
        modules.sort_by_key(|(k, _)| k.to_string());
        for (path, info) in modules {
            path.hash(state);
            info.hash(state);
        }

        // Hash files in sorted order for determinism
        let mut files: Vec<_> = self.files.iter().collect();
        files.sort_by_key(|(k, _)| k.0);
        for (id, info) in files {
            id.hash(state);
            info.hash(state);
        }
    }
}

// Implement Input for WorkspaceSnapshot as a singleton input keyed by ().
impl Input for WorkspaceSnapshot {
    type Key = ();
    type Value = WorkspaceSnapshot;

    const NAME: &'static str = "WorkspaceSnapshot";

    fn fingerprint(value: &Self::Value) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn workspace_snapshot_can_add_files() {
        let mut snapshot = WorkspaceSnapshot::new();

        let file_path = FilePath::from("src/main.ray");
        let module_path = ModulePath::from("main");

        let id = snapshot.add_file(file_path.clone(), module_path.clone());

        assert!(snapshot.files.contains_key(&id));
        assert_eq!(snapshot.file_info(id).unwrap().path, file_path);
        assert_eq!(snapshot.file_info(id).unwrap().module_path, module_path);
        assert_eq!(snapshot.file_id(&file_path), Some(id));
    }

    #[test]
    fn workspace_snapshot_reuses_file_ids() {
        let mut snapshot = WorkspaceSnapshot::new();

        let file_path = FilePath::from("src/main.ray");
        let module_path = ModulePath::from("main");

        let id1 = snapshot.add_file(file_path.clone(), module_path.clone());
        let id2 = snapshot.add_file(file_path.clone(), module_path.clone());

        assert_eq!(id1, id2);
    }

    #[test]
    fn workspace_snapshot_tracks_module_files() {
        let mut snapshot = WorkspaceSnapshot::new();

        let module_path = ModulePath::from("mymodule");
        let file1 = FilePath::from("src/mymodule/a.ray");
        let file2 = FilePath::from("src/mymodule/b.ray");

        let id1 = snapshot.add_file(file1, module_path.clone());
        let id2 = snapshot.add_file(file2, module_path.clone());

        let module_info = snapshot.module_info(&module_path).unwrap();
        assert!(module_info.files.contains(&id1));
        assert!(module_info.files.contains(&id2));
        assert_eq!(module_info.files.len(), 2);
    }

    #[test]
    fn database_can_set_and_get_file_source() {
        let db = Database::new();

        let file_id = FileId(0);
        let source = "fn main() { }".to_string();

        FileSource::new(&db, file_id, source.clone());
        let retrieved = db.get_input::<FileSource>(file_id);

        assert_eq!(retrieved.0, source);
    }

    #[test]
    fn file_source_fingerprint_changes_with_content() {
        let source1 = FileSource("fn main() { }".to_string());
        let source2 = FileSource("fn main() { x }".to_string());

        let fp1 = FileSource::fingerprint(&source1);
        let fp2 = FileSource::fingerprint(&source2);

        assert_ne!(fp1, fp2);
    }

    #[test]
    fn file_source_fingerprint_stable_for_same_content() {
        let source = FileSource("fn main() { }".to_string());

        let fp1 = FileSource::fingerprint(&source);
        let fp2 = FileSource::fingerprint(&source);

        assert_eq!(fp1, fp2);
    }

    #[test]
    fn from_directory_discovers_files() {
        use std::fs;
        use tempfile::tempdir;

        let dir = tempdir().unwrap();
        let root = dir.path();

        // Create module structure:
        // mymodule/
        //   mod.ray
        //   helper.ray
        //   sub/
        //     mod.ray
        let module_dir = root.join("mymodule");
        fs::create_dir(&module_dir).unwrap();
        fs::write(module_dir.join("mod.ray"), "fn main() {}").unwrap();
        fs::write(module_dir.join("helper.ray"), "fn help() {}").unwrap();

        let sub_dir = module_dir.join("sub");
        fs::create_dir(&sub_dir).unwrap();
        fs::write(sub_dir.join("mod.ray"), "fn sub_fn() {}").unwrap();

        let snapshot = WorkspaceSnapshot::from_directory(&FilePath::from(module_dir)).unwrap();

        // Should have discovered files
        assert_eq!(snapshot.files.len(), 3);

        // Should have two modules: mymodule and mymodule::sub
        assert!(snapshot.modules.contains_key(&ModulePath::from("mymodule")));
        assert!(
            snapshot
                .modules
                .contains_key(&ModulePath::from("mymodule::sub"))
        );

        // Root module should be marked
        assert!(
            snapshot
                .module_info(&ModulePath::from("mymodule"))
                .unwrap()
                .is_root
        );
    }

    #[test]
    fn with_overlay_adds_new_files() {
        let mut snapshot = WorkspaceSnapshot::new();
        let existing_path = FilePath::from("src/existing.ray");
        snapshot.add_file(existing_path.clone(), ModulePath::from("existing"));

        let mut overlay = HashMap::new();
        let new_path = FilePath::from("src/new.ray");
        overlay.insert(new_path.clone(), "fn new() {}".to_string());

        let updated = snapshot.with_overlay(&overlay);

        // Original file still exists
        assert!(updated.file_id(&existing_path).is_some());

        // New file was added
        assert!(updated.file_id(&new_path).is_some());
    }

    #[test]
    fn with_overlay_preserves_existing_file_ids() {
        let mut snapshot = WorkspaceSnapshot::new();
        let path = FilePath::from("src/test.ray");
        let original_id = snapshot.add_file(path.clone(), ModulePath::from("test"));

        let mut overlay = HashMap::new();
        overlay.insert(path.clone(), "modified content".to_string());

        let updated = snapshot.with_overlay(&overlay);

        // File ID should be preserved
        assert_eq!(updated.file_id(&path), Some(original_id));
    }

    #[test]
    fn all_file_ids_returns_all_files() {
        let mut snapshot = WorkspaceSnapshot::new();
        let id1 = snapshot.add_file(FilePath::from("a.ray"), ModulePath::from("a"));
        let id2 = snapshot.add_file(FilePath::from("b.ray"), ModulePath::from("b"));

        let all_ids: Vec<_> = snapshot.all_file_ids().collect();
        assert_eq!(all_ids.len(), 2);
        assert!(all_ids.contains(&id1));
        assert!(all_ids.contains(&id2));
    }

    #[test]
    fn all_module_paths_returns_all_modules() {
        let mut snapshot = WorkspaceSnapshot::new();
        snapshot.add_file(FilePath::from("a.ray"), ModulePath::from("mod_a"));
        snapshot.add_file(FilePath::from("b.ray"), ModulePath::from("mod_b"));

        let all_paths: Vec<_> = snapshot.all_module_paths().collect();
        assert_eq!(all_paths.len(), 2);
        assert!(all_paths.contains(&&ModulePath::from("mod_a")));
        assert!(all_paths.contains(&&ModulePath::from("mod_b")));
    }
}
