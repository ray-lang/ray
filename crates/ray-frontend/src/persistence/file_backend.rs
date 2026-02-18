use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use super::{CacheMeta, PersistenceBackend, QueryId};

/// Bump this to invalidate all file-based caches.
const CACHE_VERSION: u64 = 1;

/// On-disk format for metadata files.
#[derive(serde::Serialize, serde::Deserialize)]
struct MetaFile {
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

/// File-per-entry persistence backend with meta/value split.
///
/// Directory layout:
/// ```text
/// .ray/cache/
///   version
///   <query_id>/
///     <key_hash>.meta    # bincode(MetaFile { key_bytes, metadata_bytes })
///     <key_hash>.value   # raw value_bytes
/// ```
pub struct FileBackend {
    cache_dir: PathBuf,
    staged_writes: Mutex<Vec<StagedEntry>>,
    staged_deletes: Mutex<Vec<StagedDelete>>,
}

impl FileBackend {
    pub fn new(cache_dir: PathBuf) -> Self {
        let backend = Self {
            cache_dir,
            staged_writes: Mutex::new(Vec::new()),
            staged_deletes: Mutex::new(Vec::new()),
        };

        if !backend.check_version() {
            backend.invalidate();
        }

        backend
    }

    pub fn cache_dir(&self) -> &Path {
        &self.cache_dir
    }

    fn query_dir(&self, query: QueryId) -> PathBuf {
        self.cache_dir.join(format!("{}", query.0))
    }

    fn meta_path(&self, query: QueryId, key_hash: u64) -> PathBuf {
        self.query_dir(query)
            .join(format!("{:016x}.meta", key_hash))
    }

    fn value_path(&self, query: QueryId, key_hash: u64) -> PathBuf {
        self.query_dir(query)
            .join(format!("{:016x}.value", key_hash))
    }

    fn version_path(&self) -> PathBuf {
        self.cache_dir.join("version")
    }

    fn check_version(&self) -> bool {
        let Ok(bytes) = fs::read(self.version_path()) else {
            return false;
        };
        if bytes.len() != 8 {
            return false;
        }
        let version = u64::from_le_bytes(bytes.try_into().unwrap());
        version == CACHE_VERSION
    }

    fn write_version(&self) -> io::Result<()> {
        fs::write(self.version_path(), CACHE_VERSION.to_le_bytes())
    }

    fn invalidate(&self) {
        let _ = fs::remove_dir_all(&self.cache_dir);
    }
}

impl PersistenceBackend for FileBackend {
    fn load_all_meta(&self, query: QueryId, f: &mut dyn FnMut(u64, CacheMeta)) -> io::Result<()> {
        let dir = self.query_dir(query);
        let entries = match fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
            Err(e) => return Err(e),
        };

        for entry in entries {
            let entry = entry?;
            let path = entry.path();
            let Some(ext) = path.extension() else {
                continue;
            };
            if ext != "meta" {
                continue;
            }

            let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
                continue;
            };
            let Ok(key_hash) = u64::from_str_radix(stem, 16) else {
                continue;
            };

            let Ok(bytes) = fs::read(&path) else {
                continue;
            };
            let Ok(meta_file) = bincode::deserialize::<MetaFile>(&bytes) else {
                continue;
            };

            f(
                key_hash,
                CacheMeta {
                    key_bytes: meta_file.key_bytes,
                    metadata_bytes: meta_file.metadata_bytes,
                },
            );
        }

        Ok(())
    }

    fn load_meta(&self, query: QueryId, key_hash: u64) -> io::Result<Option<CacheMeta>> {
        let path = self.meta_path(query, key_hash);
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e),
        };

        let meta_file: MetaFile = bincode::deserialize(&bytes)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        Ok(Some(CacheMeta {
            key_bytes: meta_file.key_bytes,
            metadata_bytes: meta_file.metadata_bytes,
        }))
    }

    fn load_value(&self, query: QueryId, key_hash: u64) -> io::Result<Option<Vec<u8>>> {
        let path = self.value_path(query, key_hash);
        match fs::read(&path) {
            Ok(bytes) => Ok(Some(bytes)),
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e),
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

        fs::create_dir_all(&self.cache_dir)?;

        // Process deletes
        for delete in &deletes {
            let meta_path = self.meta_path(delete.query, delete.key_hash);
            let value_path = self.value_path(delete.query, delete.key_hash);
            let _ = fs::remove_file(&meta_path);
            let _ = fs::remove_file(&value_path);
        }

        // Process writes (atomic via temp + rename)
        for entry in &writes {
            let dir = self.query_dir(entry.query);
            fs::create_dir_all(&dir)?;

            let meta_file = MetaFile {
                key_bytes: entry.key_bytes.clone(),
                metadata_bytes: entry.metadata_bytes.clone(),
            };
            let meta_bytes =
                bincode::serialize(&meta_file).map_err(|e| io::Error::other(e.to_string()))?;

            // Write meta file atomically
            let meta_final = self.meta_path(entry.query, entry.key_hash);
            let meta_tmp = dir.join(format!("{:016x}.meta.tmp", entry.key_hash));
            fs::write(&meta_tmp, &meta_bytes)?;
            fs::rename(&meta_tmp, &meta_final)?;

            // Write value file atomically
            let value_final = self.value_path(entry.query, entry.key_hash);
            let value_tmp = dir.join(format!("{:016x}.value.tmp", entry.key_hash));
            fs::write(&value_tmp, &entry.value_bytes)?;
            fs::rename(&value_tmp, &value_final)?;
        }

        self.write_version()?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use tempfile::tempdir;

    use crate::persistence::{
        PersistenceBackend as _, QueryId,
        file_backend::{CACHE_VERSION, FileBackend},
    };

    #[test]
    fn new_backend_invalidates_when_no_version_file() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");

        fs::create_dir_all(cache_dir.join("1")).unwrap();
        fs::write(cache_dir.join("1/0000000000000001.meta"), b"stale").unwrap();

        let _backend = FileBackend::new(cache_dir.clone());

        assert!(!cache_dir.join("1").exists());
    }

    #[test]
    fn new_backend_invalidates_on_version_mismatch() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        fs::create_dir_all(&cache_dir).unwrap();

        fs::write(cache_dir.join("version"), (CACHE_VERSION + 1).to_le_bytes()).unwrap();
        fs::create_dir_all(cache_dir.join("1")).unwrap();
        fs::write(cache_dir.join("1/data.meta"), b"old").unwrap();

        let _backend = FileBackend::new(cache_dir.clone());

        assert!(!cache_dir.join("1").exists());
    }

    #[test]
    fn new_backend_preserves_on_version_match() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        fs::create_dir_all(cache_dir.join("1")).unwrap();

        fs::write(cache_dir.join("version"), CACHE_VERSION.to_le_bytes()).unwrap();
        fs::write(cache_dir.join("1/data.meta"), b"keep").unwrap();

        let _backend = FileBackend::new(cache_dir.clone());

        assert_eq!(fs::read(cache_dir.join("1/data.meta")).unwrap(), b"keep");
    }

    #[test]
    fn stage_write_and_flush_creates_files() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir.clone());

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

        assert!(cache_dir.join("1/000000000000002a.meta").exists());
        assert!(cache_dir.join("1/000000000000002a.value").exists());

        let version_bytes = fs::read(cache_dir.join("version")).unwrap();
        let version = u64::from_le_bytes(version_bytes.try_into().unwrap());
        assert_eq!(version, CACHE_VERSION);
    }

    #[test]
    fn load_meta_returns_written_data() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir);

        let query = QueryId(1);
        backend
            .stage_write(
                query,
                123,
                b"mykey".to_vec(),
                b"mymeta".to_vec(),
                b"myvalue".to_vec(),
            )
            .unwrap();
        backend.flush().unwrap();

        let meta = backend.load_meta(query, 123).unwrap().unwrap();
        assert_eq!(meta.key_bytes, b"mykey");
        assert_eq!(meta.metadata_bytes, b"mymeta");
    }

    #[test]
    fn load_value_returns_written_data() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir);

        let query = QueryId(1);
        backend
            .stage_write(
                query,
                123,
                b"mykey".to_vec(),
                b"mymeta".to_vec(),
                b"myvalue".to_vec(),
            )
            .unwrap();
        backend.flush().unwrap();

        let value = backend.load_value(query, 123).unwrap().unwrap();
        assert_eq!(value, b"myvalue");
    }

    #[test]
    fn load_meta_returns_none_for_missing_entry() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir);

        assert!(backend.load_meta(QueryId(1), 999).unwrap().is_none());
    }

    #[test]
    fn load_value_returns_none_for_missing_entry() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir);

        assert!(backend.load_value(QueryId(1), 999).unwrap().is_none());
    }

    #[test]
    fn flush_with_no_staged_entries_is_noop() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir.clone());

        backend.flush().unwrap();

        assert!(!cache_dir.exists());
    }

    #[test]
    fn stage_delete_removes_files() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir.clone());

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

        assert!(cache_dir.join("1/000000000000002a.meta").exists());
        assert!(cache_dir.join("1/000000000000002a.value").exists());

        backend.stage_delete(query, 42).unwrap();
        backend.flush().unwrap();

        assert!(!cache_dir.join("1/000000000000002a.meta").exists());
        assert!(!cache_dir.join("1/000000000000002a.value").exists());
    }

    #[test]
    fn load_all_meta_iterates_entries() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir);

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
    fn load_all_meta_returns_ok_for_missing_query_dir() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir);

        let mut count = 0;
        backend
            .load_all_meta(QueryId(99), &mut |_, _| count += 1)
            .unwrap();
        assert_eq!(count, 0);
    }

    #[test]
    fn flush_overwrites_existing_entry() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let backend = FileBackend::new(cache_dir);

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
}
