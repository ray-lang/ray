use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, OnceLock};

use crate::pathlib::Path;

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct NodeId(pub u64);

static NODE_ID_NAMESPACE: AtomicU32 = AtomicU32::new(0);
static NODE_ID_COUNTERS: OnceLock<Mutex<HashMap<u32, u32>>> = OnceLock::new();

#[must_use]
pub struct NodeIdNamespaceGuard {
    prev_namespace: u32,
}

impl Drop for NodeIdNamespaceGuard {
    fn drop(&mut self) {
        NODE_ID_NAMESPACE.store(self.prev_namespace, Ordering::Relaxed);
    }
}

impl NodeId {
    pub fn new() -> Self {
        let namespace = NODE_ID_NAMESPACE.load(Ordering::Relaxed);
        let counters = NODE_ID_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
        let mut counters = counters.lock().unwrap();

        let counter = counters.entry(namespace).or_insert(1);
        let id = *counter;
        *counter = counter.checked_add(1).expect("NodeId counter overflow");

        NodeId(((namespace as u64) << 32) | (id as u64))
    }

    fn namespace_from_path(path: &Path) -> u32 {
        let hash = path.to_id();
        let namespace = (hash as u32) ^ ((hash >> 32) as u32);
        if namespace == 0 { 1 } else { namespace }
    }

    pub fn enter_namespace(path: &Path) -> NodeIdNamespaceGuard {
        let namespace = Self::namespace_from_path(path);
        let prev_namespace = NODE_ID_NAMESPACE.load(Ordering::Relaxed);

        NODE_ID_NAMESPACE.store(namespace, Ordering::Relaxed);

        NodeIdNamespaceGuard { prev_namespace }
    }
}

impl std::fmt::LowerHex for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", self.0)
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeId({})", self.0)
    }
}
