use serde::{Deserialize, Serialize};

use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    sync::{Mutex, OnceLock},
};

use crate::{def::DefId, pathlib::Path};

/// Identifies an AST node within a top-level definition.
///
/// NodeIds are used to map between AST nodes and their associated metadata
/// (source spans, inferred types, diagnostics).
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct NodeId {
    /// The definition containing this node.
    pub owner: DefId,
    /// A sequential index assigned during indexing of the owner.
    pub index: u32,
}

static CURRENT_DEF_ID: Mutex<Option<DefId>> = Mutex::new(None);
static NODE_ID_COUNTERS: OnceLock<Mutex<HashMap<DefId, u32>>> = OnceLock::new();

#[must_use]
pub struct NodeIdGuard {
    prev_def_id: Option<DefId>,
}

impl Drop for NodeIdGuard {
    fn drop(&mut self) {
        let mut lock = CURRENT_DEF_ID.lock().unwrap_or_else(|e| e.into_inner());
        *lock = self.prev_def_id;
    }
}

impl NodeId {
    pub fn new() -> Self {
        let owner = CURRENT_DEF_ID
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .expect("NodeId::new() called outside of enter_def scope");
        let counters = NODE_ID_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
        let mut counters = counters.lock().unwrap_or_else(|e| e.into_inner());

        let counter = counters.entry(owner).or_insert(1);
        let index = *counter;
        *counter = counter.checked_add(1).expect("NodeId counter overflow");

        NodeId { owner, index }
    }

    pub fn enter_def(def_id: DefId) -> NodeIdGuard {
        let prev_def_id = CURRENT_DEF_ID
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .replace(def_id);

        // Reset counter for this DefId to get deterministic NodeIds on re-parse
        let counters = NODE_ID_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
        counters
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(def_id, 1);

        NodeIdGuard { prev_def_id }
    }

    /// Like `enter_def`, but does NOT reset the counter.
    /// Use this when creating additional nodes for an already-parsed definition
    /// (e.g. during AST desugaring/transformation passes).
    pub fn resume_def(def_id: DefId) -> NodeIdGuard {
        let prev_def_id = CURRENT_DEF_ID
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .replace(def_id);

        // Ensure counter exists but do NOT reset it
        let counters = NODE_ID_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
        counters
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .entry(def_id)
            .or_insert(1);

        NodeIdGuard { prev_def_id }
    }

    pub fn enter_namespace(_path: &Path) -> NodeIdGuard {
        unreachable!()
        // let namespace = Self::namespace_from_path(path);
        // let prev_namespace = CURRENT_DEF_ID.load(Ordering::Relaxed);

        // CURRENT_DEF_ID.store(namespace, Ordering::Relaxed);

        // NodeIdGuard {
        //     prev_def_id: prev_namespace,
        // }
    }
}

impl std::fmt::LowerHex for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut hasher = fnv::FnvHasher::default();
        self.owner.hash(&mut hasher);
        self.index.hash(&mut hasher);
        let out = hasher.finish();
        write!(f, "{:x}", out)
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeId(owner={}, index={})", self.owner, self.index)
    }
}
