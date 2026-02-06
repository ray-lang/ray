//! Module path type for the incremental compiler.
//!
//! A `ModulePath` identifies a module (directory or single-file module) in the workspace.
//! It is distinct from `Path` which can include type arguments and other path parts.

use std::fmt;

use serde::{Deserialize, Serialize};

use super::Path;

/// A module path identifying a module in the workspace.
///
/// Module paths correspond to directories or single-file modules.
/// They are used as keys in WorkspaceSnapshot.modules and for library lookup.
///
/// Examples: `core`, `std::io`, `myproject::utils`
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ModulePath(Vec<String>);

impl ModulePath {
    /// Create a new module path from a vector of segments.
    pub fn new(segments: Vec<String>) -> Self {
        Self(segments)
    }

    /// Create an empty module path (root).
    pub fn root() -> Self {
        Self(Vec::new())
    }

    /// Get the segments of the module path.
    pub fn segments(&self) -> &[String] {
        &self.0
    }

    /// Get the short name (last segment) of the module path.
    pub fn short_name(&self) -> String {
        self.0.last().cloned().unwrap_or_default()
    }

    /// Check if this module path is empty (root).
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get the number of segments in the module path.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Convert to a `Path` (for compatibility with existing code).
    pub fn to_path(&self) -> Path {
        Path::from(self.0.join("::").as_str())
    }

    /// Check if this module path starts with the given prefix.
    ///
    /// Returns true if the first segments of this path match all segments of the prefix.
    /// Resolve `super` segments relative to the given current module.
    ///
    /// Each `super` segment pops one level off `current_module` and is removed
    /// from the path. The remaining segments are appended to the resolved parent.
    ///
    /// Example: if current module is `core::io` and path is `super`,
    /// the result is `core`.
    pub fn resolve_super(&self, current_module: &ModulePath) -> ModulePath {
        let mut parent = current_module.0.clone();
        let mut remaining = Vec::new();
        for seg in &self.0 {
            if seg == "super" {
                parent.pop();
            } else {
                remaining.push(seg.clone());
            }
        }
        parent.extend(remaining);
        ModulePath(parent)
    }

    /// Returns true if this path contains a `super` segment.
    pub fn has_super(&self) -> bool {
        self.0.iter().any(|s| s == "super")
    }

    /// Check if this module path starts with the given prefix.
    ///
    /// Returns true if the first segments of this path match all segments of the prefix.
    pub fn starts_with(&self, prefix: &str) -> bool {
        let prefix_segments: Vec<&str> = if prefix.is_empty() {
            vec![]
        } else {
            prefix.split("::").collect()
        };

        if prefix_segments.len() > self.0.len() {
            return false;
        }

        self.0
            .iter()
            .zip(prefix_segments.iter())
            .all(|(a, b)| a == *b)
    }
}

impl From<&str> for ModulePath {
    fn from(s: &str) -> Self {
        if s.is_empty() {
            Self(Vec::new())
        } else {
            Self(s.split("::").map(String::from).collect())
        }
    }
}

impl From<String> for ModulePath {
    fn from(s: String) -> Self {
        Self::from(s.as_str())
    }
}

impl From<&Path> for ModulePath {
    fn from(path: &Path) -> Self {
        Self(path.to_name_vec())
    }
}

impl From<Path> for ModulePath {
    fn from(path: Path) -> Self {
        Self::from(&path)
    }
}

impl fmt::Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.join("::"))
    }
}

#[cfg(test)]
mod tests {
    use crate::pathlib::{ModulePath, Path};

    #[test]
    fn module_path_from_str() {
        let path = ModulePath::from("std::io");
        assert_eq!(path.segments(), &["std", "io"]);
        assert_eq!(path.short_name(), "io");
    }

    #[test]
    fn module_path_empty() {
        let path = ModulePath::from("");
        assert!(path.is_empty());
        assert_eq!(path.len(), 0);
    }

    #[test]
    fn module_path_display() {
        let path = ModulePath::from("std::io");
        assert_eq!(path.to_string(), "std::io");
    }

    #[test]
    fn module_path_from_path() {
        let path = Path::from("std::io");
        let module_path = ModulePath::from(&path);
        assert_eq!(module_path.segments(), &["std", "io"]);
    }

    #[test]
    fn module_path_starts_with() {
        let path = ModulePath::from("core::io::file");
        assert!(path.starts_with("core"));
        assert!(path.starts_with("core::io"));
        assert!(path.starts_with("core::io::file"));
        assert!(!path.starts_with("core::io::file::extra"));
        assert!(!path.starts_with("std"));
        assert!(!path.starts_with("cor"));
    }
}
