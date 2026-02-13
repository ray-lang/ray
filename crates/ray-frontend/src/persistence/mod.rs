pub mod file_backend;

use std::io;

use serde::{Deserialize, Serialize};

/// Stable numeric identifier for a query type.
/// Computed as FNV-1a hash of `Query::NAME` at compile time.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct QueryId(pub u32);

/// Metadata for a cached query entry (no value bytes).
/// Used for dep validation without deserializing the full value.
pub struct CacheMeta {
    pub key_bytes: Vec<u8>,
    pub metadata_bytes: Vec<u8>,
}

/// Metadata stored alongside a cached query result.
/// Serialized into `CacheMeta::metadata_bytes`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EntryMetadata {
    pub fingerprint: u64,
    pub input_deps: Vec<DepRecord>,
    pub query_deps: Vec<DepRecord>,
}

/// A dependency reference stored in `EntryMetadata`.
/// Uses raw `u32` for `query_id` for cleaner serde.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DepRecord {
    pub query_id: u32,
    pub key_hash: u64,
    pub fingerprint: u64,
}

/// Abstraction over the persistent storage backend for query results.
///
/// All mutation methods use `&self` with interior mutability
/// (e.g., `Mutex<Vec<StagedEntry>>`), so the `Database` can hold
/// `Option<Box<dyn PersistenceBackend>>` without an outer lock.
pub trait PersistenceBackend: Send + Sync {
    /// Load all metadata for a query type. Backend controls iteration.
    fn load_all_meta(&self, query: QueryId, f: &mut dyn FnMut(u64, CacheMeta)) -> io::Result<()>;

    /// Load metadata for a single entry.
    fn load_meta(&self, query: QueryId, key_hash: u64) -> io::Result<Option<CacheMeta>>;

    /// Load the value bytes for a single entry (only after meta validation passes).
    fn load_value(&self, query: QueryId, key_hash: u64) -> io::Result<Option<Vec<u8>>>;

    /// Stage a write (not yet persisted).
    fn stage_write(
        &self,
        query: QueryId,
        key_hash: u64,
        key_bytes: Vec<u8>,
        metadata_bytes: Vec<u8>,
        value_bytes: Vec<u8>,
    ) -> io::Result<()>;

    /// Stage a deletion (not yet persisted).
    fn stage_delete(&self, query: QueryId, key_hash: u64) -> io::Result<()>;

    /// Persist all staged writes/deletes.
    fn flush(&self) -> io::Result<()>;
}
