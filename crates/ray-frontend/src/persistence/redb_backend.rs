use std::{
    io,
    path::{Path, PathBuf},
    sync::Mutex,
};

use redb::{ReadableDatabase, TableDefinition};
use serde::{Deserialize, Serialize};

use crate::persistence::{CacheMeta, PersistenceBackend, QueryId};

/// Bump this to invalidate all redb caches.
const CACHE_VERSION: u64 = 1;

/// Table definitions.
/// Key: (query_id, key_hash), Value: serialized bytes.
const META_TABLE: TableDefinition<(u32, u64), &[u8]> = TableDefinition::new("meta");
const VALUE_TABLE: TableDefinition<(u32, u64), &[u8]> = TableDefinition::new("values");
const INFO_TABLE: TableDefinition<&str, u64> = TableDefinition::new("info");

/// On-disk format for metadata entries.
#[derive(Serialize, Deserialize)]
struct PackedMeta {
    key_bytes: Vec<u8>,
    metadata_bytes: Vec<u8>,
}

struct StagedEntry {
    query: QueryId,
    key_hash: u64,
    key_bytes: Vec<u8>,
    metadata_bytes: Vec<u8>,
    value_bytes: Vec<u8>,
}

struct StagedDelete {
    query: QueryId,
    key_hash: u64,
}

/// Redb-backed persistence backend.
///
/// Stores all query cache entries in a single redb database file
/// with B-tree indexed lookups instead of per-file I/O.
pub struct RedbBackend {
    db: redb::Database,
    staged_writes: Mutex<Vec<StagedEntry>>,
    staged_deletes: Mutex<Vec<StagedDelete>>,
}

fn to_io(e: impl std::fmt::Display) -> io::Error {
    io::Error::new(io::ErrorKind::Other, e.to_string())
}

impl RedbBackend {
    pub fn new(path: PathBuf) -> io::Result<Self> {
        // Ensure parent directory exists
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        let db = if path.exists() {
            let db = redb::Database::create(&path).map_err(to_io)?;
            if !Self::check_version(&db)? {
                drop(db);
                std::fs::remove_file(&path)?;
                Self::create_fresh(&path)?
            } else {
                db
            }
        } else {
            Self::create_fresh(&path)?
        };

        Ok(Self {
            db,
            staged_writes: Mutex::new(Vec::new()),
            staged_deletes: Mutex::new(Vec::new()),
        })
    }

    fn create_fresh(path: &Path) -> io::Result<redb::Database> {
        let db = redb::Database::create(path).map_err(to_io)?;
        let txn = db.begin_write().map_err(to_io)?;
        {
            let mut info = txn.open_table(INFO_TABLE).map_err(to_io)?;
            info.insert("version", CACHE_VERSION).map_err(to_io)?;
        }
        txn.commit().map_err(to_io)?;
        Ok(db)
    }

    fn check_version(db: &redb::Database) -> io::Result<bool> {
        let txn = db.begin_read().map_err(to_io)?;
        let table = match txn.open_table(INFO_TABLE) {
            Ok(table) => table,
            Err(redb::TableError::TableDoesNotExist(_)) => return Ok(false),
            Err(e) => return Err(to_io(e)),
        };
        match table.get("version").map_err(to_io)? {
            Some(guard) => Ok(guard.value() == CACHE_VERSION),
            None => Ok(false),
        }
    }
}

impl PersistenceBackend for RedbBackend {
    fn load_all_meta(&self, query: QueryId, f: &mut dyn FnMut(u64, CacheMeta)) -> io::Result<()> {
        let txn = self.db.begin_read().map_err(to_io)?;
        let table = match txn.open_table(META_TABLE) {
            Ok(table) => table,
            Err(redb::TableError::TableDoesNotExist(_)) => return Ok(()),
            Err(e) => return Err(to_io(e)),
        };

        let range = table
            .range((query.0, 0u64)..=(query.0, u64::MAX))
            .map_err(to_io)?;

        for entry in range {
            let (key, value) = entry.map_err(to_io)?;
            let (_qid, key_hash) = key.value();
            let packed: PackedMeta = bincode::deserialize(value.value())
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
            f(
                key_hash,
                CacheMeta {
                    key_bytes: packed.key_bytes,
                    metadata_bytes: packed.metadata_bytes,
                },
            );
        }

        Ok(())
    }

    fn load_meta(&self, query: QueryId, key_hash: u64) -> io::Result<Option<CacheMeta>> {
        let txn = self.db.begin_read().map_err(to_io)?;
        let table = match txn.open_table(META_TABLE) {
            Ok(table) => table,
            Err(redb::TableError::TableDoesNotExist(_)) => return Ok(None),
            Err(e) => return Err(to_io(e)),
        };

        match table.get((query.0, key_hash)).map_err(to_io)? {
            Some(guard) => {
                let packed: PackedMeta = bincode::deserialize(guard.value())
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
                Ok(Some(CacheMeta {
                    key_bytes: packed.key_bytes,
                    metadata_bytes: packed.metadata_bytes,
                }))
            }
            None => Ok(None),
        }
    }

    fn load_value(&self, query: QueryId, key_hash: u64) -> io::Result<Option<Vec<u8>>> {
        let txn = self.db.begin_read().map_err(to_io)?;
        let table = match txn.open_table(VALUE_TABLE) {
            Ok(table) => table,
            Err(redb::TableError::TableDoesNotExist(_)) => return Ok(None),
            Err(e) => return Err(to_io(e)),
        };

        match table.get((query.0, key_hash)).map_err(to_io)? {
            Some(guard) => Ok(Some(guard.value().to_vec())),
            None => Ok(None),
        }
    }

    fn stage_write(
        &self,
        query: QueryId,
        key_hash: u64,
        key_bytes: Vec<u8>,
        metadata_bytes: Vec<u8>,
        value_bytes: Vec<u8>,
    ) -> io::Result<()> {
        let mut staged = self
            .staged_writes
            .lock()
            .expect("staged_writes lock poisoned");
        staged.push(StagedEntry {
            query,
            key_hash,
            key_bytes,
            metadata_bytes,
            value_bytes,
        });
        Ok(())
    }

    fn stage_delete(&self, query: QueryId, key_hash: u64) -> io::Result<()> {
        let mut staged = self
            .staged_deletes
            .lock()
            .expect("staged_deletes lock poisoned");
        staged.push(StagedDelete { query, key_hash });
        Ok(())
    }

    fn flush(&self) -> io::Result<()> {
        let writes = {
            let mut staged = self
                .staged_writes
                .lock()
                .expect("staged_writes lock poisoned");
            std::mem::take(&mut *staged)
        };
        let deletes = {
            let mut staged = self
                .staged_deletes
                .lock()
                .expect("staged_deletes lock poisoned");
            std::mem::take(&mut *staged)
        };

        if writes.is_empty() && deletes.is_empty() {
            return Ok(());
        }

        let txn = self.db.begin_write().map_err(to_io)?;
        {
            let mut meta_table = txn.open_table(META_TABLE).map_err(to_io)?;
            let mut value_table = txn.open_table(VALUE_TABLE).map_err(to_io)?;

            for del in &deletes {
                meta_table
                    .remove((del.query.0, del.key_hash))
                    .map_err(to_io)?;
                value_table
                    .remove((del.query.0, del.key_hash))
                    .map_err(to_io)?;
            }

            for entry in &writes {
                let packed = PackedMeta {
                    key_bytes: entry.key_bytes.clone(),
                    metadata_bytes: entry.metadata_bytes.clone(),
                };
                let meta_bytes = bincode::serialize(&packed)
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

                meta_table
                    .insert((entry.query.0, entry.key_hash), meta_bytes.as_slice())
                    .map_err(to_io)?;
                value_table
                    .insert(
                        (entry.query.0, entry.key_hash),
                        entry.value_bytes.as_slice(),
                    )
                    .map_err(to_io)?;
            }
        }
        txn.commit().map_err(to_io)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn new_backend_creates_fresh_db() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");

        let _backend = RedbBackend::new(path.clone()).unwrap();

        assert!(path.exists());
    }

    #[test]
    fn new_backend_invalidates_on_version_mismatch() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");

        // Create a db with wrong version
        {
            let db = redb::Database::create(&path).unwrap();
            let txn = db.begin_write().unwrap();
            {
                let mut info = txn.open_table(INFO_TABLE).unwrap();
                info.insert("version", CACHE_VERSION + 1).unwrap();
            }
            txn.commit().unwrap();
        }

        // Should recreate the db
        let backend = RedbBackend::new(path).unwrap();

        // Should be empty (no stale data)
        let mut count = 0;
        backend
            .load_all_meta(QueryId(1), &mut |_, _| count += 1)
            .unwrap();
        assert_eq!(count, 0);
    }

    #[test]
    fn stage_write_and_flush() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        let query = QueryId(1);
        backend
            .stage_write(
                query,
                42,
                b"key".to_vec(),
                b"meta".to_vec(),
                b"value".to_vec(),
            )
            .unwrap();
        backend.flush().unwrap();

        let meta = backend.load_meta(query, 42).unwrap().unwrap();
        assert_eq!(meta.key_bytes, b"key");
        assert_eq!(meta.metadata_bytes, b"meta");

        let value = backend.load_value(query, 42).unwrap().unwrap();
        assert_eq!(value, b"value");
    }

    #[test]
    fn load_meta_returns_none_for_missing_entry() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        assert!(backend.load_meta(QueryId(1), 999).unwrap().is_none());
    }

    #[test]
    fn load_value_returns_none_for_missing_entry() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        assert!(backend.load_value(QueryId(1), 999).unwrap().is_none());
    }

    #[test]
    fn flush_with_no_staged_entries_is_noop() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        backend.flush().unwrap();
    }

    #[test]
    fn stage_delete_removes_entries() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        let query = QueryId(1);
        backend
            .stage_write(
                query,
                42,
                b"key".to_vec(),
                b"meta".to_vec(),
                b"value".to_vec(),
            )
            .unwrap();
        backend.flush().unwrap();

        assert!(backend.load_meta(query, 42).unwrap().is_some());
        assert!(backend.load_value(query, 42).unwrap().is_some());

        backend.stage_delete(query, 42).unwrap();
        backend.flush().unwrap();

        assert!(backend.load_meta(query, 42).unwrap().is_none());
        assert!(backend.load_value(query, 42).unwrap().is_none());
    }

    #[test]
    fn load_all_meta_iterates_entries() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        let query = QueryId(2);
        backend
            .stage_write(query, 1, b"k1".to_vec(), b"m1".to_vec(), b"v1".to_vec())
            .unwrap();
        backend
            .stage_write(query, 2, b"k2".to_vec(), b"m2".to_vec(), b"v2".to_vec())
            .unwrap();
        backend.flush().unwrap();

        let mut entries: Vec<(u64, Vec<u8>, Vec<u8>)> = Vec::new();
        backend
            .load_all_meta(query, &mut |key_hash, meta| {
                entries.push((key_hash, meta.key_bytes, meta.metadata_bytes));
            })
            .unwrap();

        entries.sort_by_key(|(h, _, _)| *h);
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0], (1, b"k1".to_vec(), b"m1".to_vec()));
        assert_eq!(entries[1], (2, b"k2".to_vec(), b"m2".to_vec()));
    }

    #[test]
    fn load_all_meta_returns_ok_for_missing_query() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        let mut count = 0;
        backend
            .load_all_meta(QueryId(99), &mut |_, _| count += 1)
            .unwrap();
        assert_eq!(count, 0);
    }

    #[test]
    fn flush_overwrites_existing_entry() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        let query = QueryId(1);
        backend
            .stage_write(
                query,
                1,
                b"old_k".to_vec(),
                b"old_m".to_vec(),
                b"old_v".to_vec(),
            )
            .unwrap();
        backend.flush().unwrap();

        backend
            .stage_write(
                query,
                1,
                b"new_k".to_vec(),
                b"new_m".to_vec(),
                b"new_v".to_vec(),
            )
            .unwrap();
        backend.flush().unwrap();

        let meta = backend.load_meta(query, 1).unwrap().unwrap();
        assert_eq!(meta.key_bytes, b"new_k");
        let value = backend.load_value(query, 1).unwrap().unwrap();
        assert_eq!(value, b"new_v");
    }

    #[test]
    fn load_all_meta_only_returns_matching_query() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("cache.redb");
        let backend = RedbBackend::new(path).unwrap();

        // Write entries for two different queries
        backend
            .stage_write(
                QueryId(1),
                10,
                b"q1k".to_vec(),
                b"q1m".to_vec(),
                b"q1v".to_vec(),
            )
            .unwrap();
        backend
            .stage_write(
                QueryId(2),
                20,
                b"q2k".to_vec(),
                b"q2m".to_vec(),
                b"q2v".to_vec(),
            )
            .unwrap();
        backend.flush().unwrap();

        let mut entries = Vec::new();
        backend
            .load_all_meta(QueryId(1), &mut |key_hash, meta| {
                entries.push((key_hash, meta.key_bytes));
            })
            .unwrap();

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0], (10, b"q1k".to_vec()));
    }
}
