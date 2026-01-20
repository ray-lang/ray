use serde::{Deserialize, Serialize};

/// Identifies a source file in the workspace.
///
/// FileIds are assigned during workspace indexing and remain stable as long
/// as the file exists. The id is an index into the workspace's file list.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct FileId(pub u32);

impl std::fmt::Display for FileId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FileId({:x})", self.0)
    }
}
