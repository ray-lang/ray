use std::hash::{DefaultHasher, Hash, Hasher};

use serde::{Deserialize, Serialize};

use crate::def::DefId;

/// Identifies a local binding (parameter, let-binding) within a definition.
///
/// LocalBindingIds are scoped to their owning definition. Two locals in different
/// functions may have the same index but different owners, making them distinct.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct LocalBindingId {
    /// The function/closure containing this local binding.
    pub owner: DefId,
    /// Sequential index within the owner (in source order).
    pub index: u32,
}

impl std::fmt::Display for LocalBindingId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::local{}", self.owner, self.index)
    }
}

impl std::fmt::LowerHex for LocalBindingId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut state = DefaultHasher::new();
        self.owner.hash(&mut state);
        self.index.hash(&mut state);
        let out = state.finish();
        write!(f, "{:x}", out)
    }
}

impl LocalBindingId {
    pub fn new(owner: DefId, index: u32) -> Self {
        Self { owner, index }
    }
}
