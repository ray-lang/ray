use std::{env, path::PathBuf};

use crate::pathlib::FilePath;

#[derive(Debug, Clone, Default)]
pub struct RayPaths {
    root: FilePath,
}

impl RayPaths {
    pub fn new(root: FilePath) -> Self {
        Self { root }
    }

    pub fn bootstrap_root() -> Self {
        if let Some(home) = home::home_dir() {
            return RayPaths::new(FilePath::from(home) / ".ray");
        }
        RayPaths::new(FilePath::from("/opt/ray"))
    }

    pub fn discover(explicit: Option<FilePath>, workspace_hint: Option<&FilePath>) -> Option<Self> {
        fn has_toolchain_root(candidate: &FilePath) -> bool {
            candidate.exists()
        }

        let mut candidates: Vec<FilePath> = Vec::new();

        if let Some(path) = explicit {
            candidates.push(path);
        }

        if let Ok(path) = env::var("RAY_PATH") {
            if !path.is_empty() {
                candidates.push(FilePath::from(PathBuf::from(path)));
            }
        }

        if let Some(hint) = workspace_hint {
            candidates.push(hint.clone());
        }

        if let Some(home) = home::home_dir() {
            candidates.push(FilePath::from(home) / ".ray");
        }

        candidates.push(FilePath::from("/opt/ray"));

        candidates
            .into_iter()
            .find(|candidate| has_toolchain_root(candidate))
            .map(Self::new)
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    pub fn get_root(&self) -> &FilePath {
        &self.root
    }

    pub fn get_bin_path(&self) -> FilePath {
        &self.root / "bin"
    }

    pub fn get_build_path(&self) -> FilePath {
        &self.root / "build"
    }

    pub fn get_lib_path(&self) -> FilePath {
        &self.root / "lib"
    }

    pub fn get_c_includes_path(&self) -> FilePath {
        &self.root / "wasi-sysroot" / "include"
    }
}
