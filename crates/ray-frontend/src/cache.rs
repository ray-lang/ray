use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use serde::{Deserialize, Serialize};

/// Bump this to invalidate all caches across all users.
pub const CACHE_VERSION: u64 = 1;

/// Represents a dependency of a cached query result.
///
/// Stores the query/input name, the FNV hash of its key, and the fingerprint
/// of the value at the time the dependent was computed.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Dependency {
    pub query_name: String,
    pub key_hash: u64,
    pub fingerprint: u64,
}

/// On-disk format for a cached query result.
///
/// Stores the serialized key (for collision detection), serialized value,
/// a fingerprint of the value, and the list of dependencies.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CacheEntry {
    pub key_bytes: Vec<u8>,
    pub value_bytes: Vec<u8>,
    pub fingerprint: u64,
    pub dependencies: Vec<Dependency>,
}

/// A staged write to be flushed to disk at the end of a successful build.
struct DirtyEntry {
    query_name: String,
    key_hash: u64,
    data: Vec<u8>,
}

/// Persistent on-disk cache for query results.
///
/// Query results are staged in memory during a build and written to disk
/// in a single batch at the end of a successful build. On the next build,
/// cached entries are loaded lazily on cache miss.
///
/// Directory layout:
/// ```text
/// .ray/cache/
///   version                       # u64, must match CACHE_VERSION
///   parse_file/
///     <key_hash>.bin              # bincode-serialized CacheEntry
///   name_resolutions/
///     <key_hash>.bin
///   ...
/// ```
pub struct DiskCache {
    cache_dir: PathBuf,
    dirty: Mutex<Vec<DirtyEntry>>,
}

impl DiskCache {
    /// Create a new DiskCache rooted at the given directory.
    ///
    /// If the directory doesn't exist, it will be created on flush.
    /// If the version file doesn't match CACHE_VERSION, the cache is invalidated.
    pub fn new(cache_dir: PathBuf) -> Self {
        let cache = Self {
            cache_dir,
            dirty: Mutex::new(Vec::new()),
        };

        if !cache.check_version() {
            cache.invalidate();
        }

        cache
    }

    /// Load a raw cache entry from disk.
    ///
    /// Returns the raw bytes of the bincode-serialized `CacheEntry`,
    /// or `None` if the entry doesn't exist or can't be read.
    pub fn load_raw(&self, query_name: &str, key_hash: u64) -> Option<Vec<u8>> {
        let path = self.entry_path(query_name, key_hash);
        fs::read(&path).ok()
    }

    /// Stage a cache entry to be written on the next flush.
    ///
    /// The `data` should be a bincode-serialized `CacheEntry`.
    pub fn stage_write(&self, query_name: &str, key_hash: u64, data: Vec<u8>) {
        let mut dirty = self.dirty.lock().expect("dirty lock poisoned");
        dirty.push(DirtyEntry {
            query_name: query_name.to_string(),
            key_hash,
            data,
        });
    }

    /// Write all staged entries to disk atomically and update the version file.
    ///
    /// Each entry is written to a temporary file first, then renamed to its
    /// final location to avoid partial writes.
    pub fn flush(&self) -> io::Result<()> {
        let entries = {
            let mut dirty = self.dirty.lock().expect("dirty lock poisoned");
            std::mem::take(&mut *dirty)
        };

        if entries.is_empty() {
            return Ok(());
        }

        // Ensure base cache directory exists
        fs::create_dir_all(&self.cache_dir)?;

        for entry in &entries {
            let dir = self.cache_dir.join(&entry.query_name);
            fs::create_dir_all(&dir)?;

            let final_path = dir.join(format!("{:016x}.bin", entry.key_hash));
            let tmp_path = dir.join(format!("{:016x}.bin.tmp", entry.key_hash));

            fs::write(&tmp_path, &entry.data)?;
            fs::rename(&tmp_path, &final_path)?;
        }

        self.write_version()?;

        Ok(())
    }

    /// Check whether the on-disk version matches CACHE_VERSION.
    pub fn check_version(&self) -> bool {
        let version_path = self.version_path();
        let Ok(bytes) = fs::read(&version_path) else {
            return false;
        };

        if bytes.len() != 8 {
            return false;
        }

        let version = u64::from_le_bytes(bytes.try_into().unwrap());
        version == CACHE_VERSION
    }

    /// Delete the entire cache directory.
    pub fn invalidate(&self) {
        let _ = fs::remove_dir_all(&self.cache_dir);
    }

    /// Returns the path to this cache's root directory.
    pub fn cache_dir(&self) -> &Path {
        &self.cache_dir
    }

    fn entry_path(&self, query_name: &str, key_hash: u64) -> PathBuf {
        self.cache_dir
            .join(query_name)
            .join(format!("{:016x}.bin", key_hash))
    }

    fn version_path(&self) -> PathBuf {
        self.cache_dir.join("version")
    }

    fn write_version(&self) -> io::Result<()> {
        fs::write(self.version_path(), CACHE_VERSION.to_le_bytes())
    }
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn new_cache_invalidates_when_no_version_file() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");

        // Create cache dir with some stale data but no version file
        fs::create_dir_all(cache_dir.join("some_query")).unwrap();
        fs::write(cache_dir.join("some_query/0000000000000001.bin"), b"stale").unwrap();

        let _cache = DiskCache::new(cache_dir.clone());

        // Cache dir should have been removed by invalidate()
        assert!(!cache_dir.join("some_query").exists());
    }

    #[test]
    fn new_cache_invalidates_on_version_mismatch() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        fs::create_dir_all(&cache_dir).unwrap();

        // Write a wrong version
        fs::write(cache_dir.join("version"), (CACHE_VERSION + 1).to_le_bytes()).unwrap();
        fs::create_dir_all(cache_dir.join("old_query")).unwrap();
        fs::write(cache_dir.join("old_query/data.bin"), b"old").unwrap();

        let _cache = DiskCache::new(cache_dir.clone());

        // Should have been invalidated
        assert!(!cache_dir.join("old_query").exists());
    }

    #[test]
    fn new_cache_preserves_on_version_match() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        fs::create_dir_all(cache_dir.join("good_query")).unwrap();

        // Write correct version
        fs::write(cache_dir.join("version"), CACHE_VERSION.to_le_bytes()).unwrap();
        fs::write(cache_dir.join("good_query/data.bin"), b"keep").unwrap();

        let _cache = DiskCache::new(cache_dir.clone());

        // Data should still be there
        assert_eq!(
            fs::read(cache_dir.join("good_query/data.bin")).unwrap(),
            b"keep"
        );
    }

    #[test]
    fn stage_write_and_flush_creates_files() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let cache = DiskCache::new(cache_dir.clone());

        cache.stage_write("my_query", 42, b"hello world".to_vec());
        cache.stage_write("my_query", 99, b"other data".to_vec());
        cache.stage_write("another_query", 1, b"data".to_vec());

        cache.flush().unwrap();

        // Verify files were created
        assert_eq!(
            fs::read(cache_dir.join("my_query/000000000000002a.bin")).unwrap(),
            b"hello world"
        );
        assert_eq!(
            fs::read(cache_dir.join("my_query/0000000000000063.bin")).unwrap(),
            b"other data"
        );
        assert_eq!(
            fs::read(cache_dir.join("another_query/0000000000000001.bin")).unwrap(),
            b"data"
        );

        // Version file should exist with correct version
        let version_bytes = fs::read(cache_dir.join("version")).unwrap();
        let version = u64::from_le_bytes(version_bytes.try_into().unwrap());
        assert_eq!(version, CACHE_VERSION);
    }

    #[test]
    fn load_raw_returns_written_data() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let cache = DiskCache::new(cache_dir);

        cache.stage_write("test_query", 123, b"cached bytes".to_vec());
        cache.flush().unwrap();

        let loaded = cache.load_raw("test_query", 123);
        assert_eq!(loaded, Some(b"cached bytes".to_vec()));
    }

    #[test]
    fn load_raw_returns_none_for_missing_entry() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let cache = DiskCache::new(cache_dir);

        assert_eq!(cache.load_raw("nonexistent", 999), None);
    }

    #[test]
    fn flush_with_no_staged_entries_is_noop() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let cache = DiskCache::new(cache_dir.clone());

        cache.flush().unwrap();

        // Cache dir should not exist since we had nothing to write
        assert!(!cache_dir.exists());
    }

    #[test]
    fn invalidate_removes_cache_directory() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let cache = DiskCache::new(cache_dir.clone());

        cache.stage_write("q", 1, b"data".to_vec());
        cache.flush().unwrap();
        assert!(cache_dir.exists());

        cache.invalidate();
        assert!(!cache_dir.exists());
    }

    #[test]
    fn check_version_false_for_missing_file() {
        let dir = tempdir().unwrap();
        let cache = DiskCache {
            cache_dir: dir.path().join("no_such_dir"),
            dirty: Mutex::new(Vec::new()),
        };
        assert!(!cache.check_version());
    }

    #[test]
    fn check_version_false_for_corrupted_file() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        fs::create_dir_all(&cache_dir).unwrap();
        fs::write(cache_dir.join("version"), b"short").unwrap();

        let cache = DiskCache {
            cache_dir,
            dirty: Mutex::new(Vec::new()),
        };
        assert!(!cache.check_version());
    }

    #[test]
    fn check_version_true_for_correct_version() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        fs::create_dir_all(&cache_dir).unwrap();
        fs::write(cache_dir.join("version"), CACHE_VERSION.to_le_bytes()).unwrap();

        let cache = DiskCache {
            cache_dir,
            dirty: Mutex::new(Vec::new()),
        };
        assert!(cache.check_version());
    }

    #[test]
    fn cache_entry_roundtrip_via_bincode() {
        let entry = CacheEntry {
            key_bytes: vec![1, 2, 3],
            value_bytes: vec![4, 5, 6, 7],
            fingerprint: 0xDEADBEEF,
            dependencies: vec![
                Dependency {
                    query_name: "input_a".to_string(),
                    key_hash: 42,
                    fingerprint: 100,
                },
                Dependency {
                    query_name: "query_b".to_string(),
                    key_hash: 99,
                    fingerprint: 200,
                },
            ],
        };

        let bytes = bincode::serialize(&entry).unwrap();
        let restored: CacheEntry = bincode::deserialize(&bytes).unwrap();

        assert_eq!(restored.key_bytes, entry.key_bytes);
        assert_eq!(restored.value_bytes, entry.value_bytes);
        assert_eq!(restored.fingerprint, entry.fingerprint);
        assert_eq!(restored.dependencies.len(), 2);
        assert_eq!(restored.dependencies[0].query_name, "input_a");
        assert_eq!(restored.dependencies[0].key_hash, 42);
        assert_eq!(restored.dependencies[0].fingerprint, 100);
        assert_eq!(restored.dependencies[1].query_name, "query_b");
    }

    #[test]
    fn flush_overwrites_existing_entry() {
        let dir = tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let cache = DiskCache::new(cache_dir.clone());

        cache.stage_write("q", 1, b"old".to_vec());
        cache.flush().unwrap();

        cache.stage_write("q", 1, b"new".to_vec());
        cache.flush().unwrap();

        let loaded = cache.load_raw("q", 1).unwrap();
        assert_eq!(loaded, b"new");
    }
}
