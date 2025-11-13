use crate::pathlib::FilePath;

/// Returns true if the directory contains a module entry file (`mod.ray` or `<basename>.ray`).
pub fn is_dir_module(dir: &FilePath) -> bool {
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

/// Returns true if the given file is itself a module root (`mod.ray` or `<dirname>.ray`).
pub fn is_module_root_file(filepath: &FilePath) -> bool {
    let file_name = match filepath.as_ref().file_name().and_then(|name| name.to_str()) {
        Some(name) => name,
        None => return false,
    };

    let base = filepath.dir().file_name();
    if file_name == "mod.ray" || file_name == format!("{base}.ray") {
        return true;
    }

    let parent_name = filepath
        .as_ref()
        .parent()
        .and_then(|p| p.file_name())
        .and_then(|name| name.to_str());

    match parent_name {
        Some(parent) => file_name == format!("{}.ray", parent),
        None => false,
    }
}

/// Given any file or directory path, return the appropriate module entry.
pub fn module_entry_path(filepath: &FilePath) -> FilePath {
    if is_module_root_file(filepath) {
        return filepath.clone();
    }

    let dir = filepath.dir();
    let base = dir.file_name();
    let candidates = [&dir / "mod.ray", &dir / format!("{base}.ray")];

    for candidate in candidates {
        if candidate.exists() {
            return candidate;
        }
    }

    filepath.clone()
}
