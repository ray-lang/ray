use std::{
    any::Any,
    collections::{HashMap, HashSet},
    hash::Hash,
    hash::Hasher,
    sync::{
        Arc, Mutex, RwLock,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    time::Instant,
};

use fnv::FnvHasher;
use ray_shared::pathlib::FilePath;
use serde::{Serialize, de::DeserializeOwned};

use crate::persistence::{DepRecord, EntryMetadata, PersistenceBackend, QueryId};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum CyclePolicy {
    Panic,
    Error,
}

pub trait Query {
    type Key: Clone + Eq + Hash + Send + Sync + Serialize + DeserializeOwned + 'static;
    type Value: Clone + Send + Sync + Serialize + DeserializeOwned + 'static;

    const NAME: &'static str;
    const ID: QueryId;
    const CYCLE_POLICY: CyclePolicy = CyclePolicy::Panic;
    /// Whether this query's results should be persisted to the persistent cache.
    /// Set to `false` via `#[query(skip_persist)]`.
    const PERSIST: bool = true;

    fn compute(db: &Database, key: Self::Key) -> Self::Value;

    fn on_cycle(_db: &Database, _key: Self::Key) -> Self::Value {
        panic!("cycle detected in query {}", Self::NAME);
    }
}

pub trait Input {
    type Key: Clone + Eq + Hash + Send + Sync + 'static;
    type Value: Clone + Send + Sync + 'static;

    const NAME: &'static str;
    const ID: QueryId;

    fn fingerprint(value: &Self::Value) -> u64;
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct InputKey {
    pub name: &'static str,
    pub key: KeyId,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct QueryKey {
    pub name: &'static str,
    pub key: KeyId,
}

#[derive(Clone, Debug)]
pub struct InputDep {
    pub key: InputKey,
    pub fingerprint: u64,
}

pub struct CachedValue {
    /// The original key, type-erased. Used by the early-exit recompute
    /// registry to recover the concrete key for force-recomputation.
    pub key: Arc<dyn Any + Send + Sync>,
    pub value: Arc<dyn Any + Send + Sync>,
    pub input_deps: Vec<InputDep>,
    pub query_deps: Vec<QueryKey>,
    /// The input revision at which this entry was last validated.
    /// If this matches `Database::revision`, the cached value is known-valid
    /// without needing to walk the dependency tree.
    pub validated_at: AtomicU64,
    /// FNV hash of the serialized value bytes. Used for early-exit: if
    /// recomputation produces the same fingerprint, downstream queries
    /// don't need revalidation.
    pub fingerprint: Option<u64>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KeyId {
    pub hash: u64,
}

/// Per-query-name aggregate stats for profiling.
#[derive(Default)]
struct QueryStats {
    hits: u64,
    misses: u64,
    total_ns: u64,
}

/// Per-query function pointers for type-erased recompute.
/// Registered lazily on first `db.query::<Q>()` invocation.
///
/// The `recompute` function is used by the **in-memory** early-exit path
/// (`force_validate_query_deps`) to force-recompute a dep and check whether
/// its fingerprint changed. This is needed when an input has actually changed
/// within a running process (e.g., LSP file edit).
///
/// Persisted validation does NOT use `recompute` — it uses metadata-only
/// fingerprint checks instead (see `validate_persisted_deps`).
#[derive(Clone, Copy)]
struct QueryFns {
    /// Force-recompute: takes the type-erased key, calls `db.query::<Q>(key)`,
    /// and returns the new fingerprint. Used ONLY by the in-memory early-exit
    /// path, NOT by disk validation.
    recompute: fn(&Database, Arc<dyn Any + Send + Sync>) -> Option<u64>,
}

pub struct Database {
    cache: RwLock<HashMap<QueryKey, CachedValue>>,
    inputs: RwLock<HashMap<InputKey, Arc<dyn Any + Send + Sync>>>,
    /// Maps input name → fingerprint function. Populated lazily by `register_input`.
    input_fingerprints: RwLock<HashMap<&'static str, fn(&dyn Any) -> u64>>,
    active_stack: Mutex<Vec<QueryKey>>,
    active_inputs: Mutex<Vec<Vec<InputDep>>>,
    active_query_deps: Mutex<Vec<Vec<QueryKey>>>,
    /// Monotonically increasing counter, bumped on every `set_input` call.
    /// Cached values whose `validated_at` matches this are known-valid without
    /// needing a full dependency-tree walk.
    revision: AtomicU64,
    /// When true, per-query timing stats are collected. Off by default.
    profiling: AtomicBool,
    /// Profiling stats per query name. Only populated when profiling is enabled.
    stats: Mutex<HashMap<&'static str, QueryStats>>,
    /// Persistent cache backend. `None` when no workspace root is detected.
    persistence: Option<Box<dyn PersistenceBackend>>,
    /// Type-erased recompute + deserialization functions for early-exit validation.
    /// Keyed by query name. Registered lazily on first query call.
    query_fns: RwLock<HashMap<&'static str, QueryFns>>,
    /// Maps QueryId → &'static str name. Populated during registration.
    /// Used for collision detection and converting DepRecord IDs to names.
    id_to_name: RwLock<HashMap<QueryId, &'static str>>,
    /// Maps &'static str name → QueryId. Populated during registration.
    /// Used for converting in-memory dep names to DepRecord IDs.
    name_to_id: RwLock<HashMap<&'static str, QueryId>>,
    /// Session-level metadata cache for persisted entries. Populated lazily
    /// from the persistence backend. Used for dep validation without loading
    /// full values.
    meta_cache: RwLock<HashMap<(QueryId, u64), EntryMetadata>>,
}

impl Database {
    pub fn new() -> Self {
        Self {
            cache: RwLock::new(HashMap::new()),
            inputs: RwLock::new(HashMap::new()),
            input_fingerprints: RwLock::new(HashMap::new()),
            active_stack: Mutex::new(Vec::new()),
            active_inputs: Mutex::new(Vec::new()),
            active_query_deps: Mutex::new(Vec::new()),
            revision: AtomicU64::new(0),
            profiling: AtomicBool::new(false),
            stats: Mutex::new(HashMap::new()),
            persistence: None,
            query_fns: RwLock::new(HashMap::new()),
            id_to_name: RwLock::new(HashMap::new()),
            name_to_id: RwLock::new(HashMap::new()),
            meta_cache: RwLock::new(HashMap::new()),
        }
    }

    /// Create a Database with a persistent cache backend.
    pub fn with_persistence(backend: Box<dyn PersistenceBackend>) -> Self {
        Self {
            persistence: Some(backend),
            ..Self::new()
        }
    }

    /// Flush all staged cache entries to the persistence backend.
    ///
    /// Should be called at the end of a successful build. No-op if there is
    /// no persistence backend configured.
    pub fn flush_persistence(&self) -> std::io::Result<()> {
        if let Some(ref p) = self.persistence {
            p.flush()
        } else {
            Ok(())
        }
    }

    /// Returns whether this database has a persistence backend configured.
    pub fn has_persistence(&self) -> bool {
        self.persistence.is_some()
    }

    /// Enable per-query profiling stats collection.
    pub fn enable_profiling(&self) {
        self.profiling.store(true, Ordering::Relaxed);
    }

    /// Print aggregate query profiling stats to stderr, sorted by total time.
    /// No-op if profiling was never enabled.
    pub fn dump_stats(&self) {
        if !self.profiling.load(Ordering::Relaxed) {
            return;
        }
        let stats = self.stats.lock().expect("stats lock poisoned");
        let mut entries: Vec<_> = stats.iter().collect();
        entries.sort_by(|a, b| b.1.total_ns.cmp(&a.1.total_ns));
        eprintln!(
            "\n{:<35} {:>8} {:>8} {:>12}",
            "QUERY", "HITS", "MISSES", "TOTAL TIME"
        );
        eprintln!("{}", "-".repeat(67));
        for (name, s) in &entries {
            let ms = s.total_ns as f64 / 1_000_000.0;
            eprintln!("{:<35} {:>8} {:>8} {:>10.1}ms", name, s.hits, s.misses, ms);
        }
        let total_ms: f64 = entries
            .iter()
            .map(|(_, s)| s.total_ns as f64 / 1_000_000.0)
            .sum();
        let total_hits: u64 = entries.iter().map(|(_, s)| s.hits).sum();
        let total_misses: u64 = entries.iter().map(|(_, s)| s.misses).sum();
        eprintln!("{}", "-".repeat(67));
        eprintln!(
            "{:<35} {:>8} {:>8} {:>10.1}ms",
            "TOTAL", total_hits, total_misses, total_ms
        );
    }

    pub fn query<Q: Query>(&self, key: Q::Key) -> Q::Value {
        let qkey = QueryKey {
            name: Q::NAME,
            key: KeyId::new(&key),
        };

        // Cycle check
        if self
            .active_stack
            .lock()
            .expect("active_stack lock poisoned")
            .iter()
            .any(|k| k == &qkey)
        {
            match Q::CYCLE_POLICY {
                CyclePolicy::Panic => panic!("cycle in query {}", Q::NAME),
                CyclePolicy::Error => return Q::on_cycle(self, key),
            }
        }

        self.register_recompute::<Q>();
        let call_start = self.profiling_start();
        self.record_parent_dep(&qkey);

        // Fast path: entry already validated at current revision
        if let Some(value) = self.try_fast_path::<Q>(&qkey) {
            self.record_stat(Q::NAME, call_start, true);
            return value;
        }

        // Slow path: push frames for cycle detection, then try revalidation
        self.push_active_frames(&qkey);

        if let Some(value) = self.try_revalidate::<Q>(&qkey) {
            self.pop_active_frames();
            self.record_stat(Q::NAME, call_start, true);
            return value;
        }
        self.clear_active_frames();

        // Try persistent cache
        if Q::PERSIST {
            if let Some(value) = self.try_load_persisted::<Q>(&qkey, &key) {
                self.pop_active_frames();
                self.record_stat(Q::NAME, call_start, true);
                return value;
            }
        }

        // Full compute
        let value = self.compute_and_store::<Q>(&qkey, key);
        self.record_stat(Q::NAME, call_start, false);
        value
    }

    /// Check if a cached entry is already validated at the current revision.
    /// Returns the cached value without any dependency walking.
    fn try_fast_path<Q: Query>(&self, qkey: &QueryKey) -> Option<Q::Value> {
        let cache = self.cache.read().expect("cache lock poisoned");
        let cached = cache.get(qkey)?;
        if cached.validated_at.load(Ordering::SeqCst) != self.revision.load(Ordering::SeqCst) {
            return None;
        }
        Some(
            cached
                .value
                .downcast_ref::<Q::Value>()
                .expect("type mismatch in query cache")
                .clone(),
        )
    }

    /// Try to revalidate a cached entry by walking its dependency tree.
    /// If all deps are still valid (early-exit), updates `validated_at`
    /// and returns the cached value. Returns `None` if revalidation fails
    /// or there is no cached entry.
    ///
    /// Caller must have already pushed active frames (for cycle detection
    /// during force-recompute).
    fn try_revalidate<Q: Query>(&self, qkey: &QueryKey) -> Option<Q::Value> {
        let (input_deps, query_deps) = {
            let cache = self.cache.read().expect("cache lock poisoned");
            let cached = cache.get(qkey)?;
            (cached.input_deps.clone(), cached.query_deps.clone())
        };

        if !self.try_validate_cached(&input_deps, &query_deps) {
            return None;
        }

        let cache = self.cache.read().expect("cache lock poisoned");
        let cached = cache.get(qkey)?;
        let current_rev = self.revision.load(Ordering::SeqCst);
        cached.validated_at.store(current_rev, Ordering::SeqCst);
        Some(
            cached
                .value
                .downcast_ref::<Q::Value>()
                .expect("type mismatch in query cache")
                .clone(),
        )
    }

    /// Compute a query from scratch, store the result in cache, and
    /// optionally stage a persistent write if persistence is enabled.
    ///
    /// Pops the active frames internally (needs the collected deps).
    fn compute_and_store<Q: Query>(&self, qkey: &QueryKey, key: Q::Key) -> Q::Value {
        let key_bytes_for_persist = if Q::PERSIST && self.has_persistence() {
            bincode::serialize(&key).ok()
        } else {
            None
        };
        let key_arc: Arc<dyn Any + Send + Sync> = Arc::new(key.clone());
        let value = Q::compute(self, key);
        let (input_deps, query_deps) = self.pop_active_frames();

        let (fingerprint, value_bytes) = match bincode::serialize(&value) {
            Ok(bytes) => {
                let mut hasher = FnvHasher::default();
                hasher.write(&bytes);
                (Some(hasher.finish()), Some(bytes))
            }
            Err(_) => (None, None),
        };

        if let (Some(key_bytes), Some(fingerprint), Some(value_bytes)) =
            (key_bytes_for_persist, fingerprint, value_bytes)
        {
            self.stage_persist::<Q>(
                qkey.key.hash,
                key_bytes,
                value_bytes,
                fingerprint,
                &input_deps,
                &query_deps,
            );
        }

        self.cache.write().expect("cache lock poisoned").insert(
            qkey.clone(),
            CachedValue {
                key: key_arc,
                value: Arc::new(value.clone()),
                input_deps,
                query_deps,
                validated_at: AtomicU64::new(self.revision.load(Ordering::SeqCst)),
                fingerprint,
            },
        );

        value
    }

    /// Record `qkey` as a dependency of the currently-computing parent query.
    fn record_parent_dep(&self, qkey: &QueryKey) {
        if let Some(parent_deps) = self
            .active_query_deps
            .lock()
            .expect("active_query_deps lock poisoned")
            .last_mut()
        {
            if !parent_deps.contains(qkey) {
                parent_deps.push(qkey.clone());
            }
        }
    }

    /// Push `qkey` onto the active stack and push fresh dependency frames.
    /// Must be called before early-exit validation so that force-recompute
    /// calls can detect cycles.
    fn push_active_frames(&self, qkey: &QueryKey) {
        self.active_stack
            .lock()
            .expect("active_stack lock poisoned")
            .push(qkey.clone());
        self.active_inputs
            .lock()
            .expect("active_inputs lock poisoned")
            .push(Vec::new());
        self.active_query_deps
            .lock()
            .expect("active_query_deps lock poisoned")
            .push(Vec::new());
    }

    /// Pop the active stack and dependency frames, returning the collected deps.
    fn pop_active_frames(&self) -> (Vec<InputDep>, Vec<QueryKey>) {
        let input_deps = self
            .active_inputs
            .lock()
            .expect("active_inputs lock poisoned")
            .pop()
            .unwrap_or_default();
        let query_deps = self
            .active_query_deps
            .lock()
            .expect("active_query_deps lock poisoned")
            .pop()
            .unwrap_or_default();
        self.active_stack
            .lock()
            .expect("active_stack lock poisoned")
            .pop();
        (input_deps, query_deps)
    }

    /// Clear the current dependency frames. Used after early-exit validation
    /// fails to discard deps recorded during force-recompute.
    fn clear_active_frames(&self) {
        self.active_inputs
            .lock()
            .expect("active_inputs lock poisoned")
            .last_mut()
            .expect("active_inputs frame missing")
            .clear();
        self.active_query_deps
            .lock()
            .expect("active_query_deps lock poisoned")
            .last_mut()
            .expect("active_query_deps frame missing")
            .clear();
    }

    /// Validate a cached entry's dependencies without recomputing it.
    /// Returns `true` if all input and query deps are still valid.
    ///
    /// Caller must have already pushed active frames (for cycle detection
    /// during force-recompute). The cache read lock must NOT be held.
    fn try_validate_cached(&self, input_deps: &[InputDep], query_deps: &[QueryKey]) -> bool {
        self.inputs_match(input_deps) && self.force_validate_query_deps(query_deps)
    }

    /// Stage a computed query result for writing to the persistence backend.
    ///
    /// Converts in-memory `InputDep`/`QueryKey` deps to `DepRecord` format
    /// (with QueryId + fingerprints), builds `EntryMetadata`, and stages
    /// key/metadata/value separately for batch writing on `flush_persistence()`.
    fn stage_persist<Q: Query>(
        &self,
        key_hash: u64,
        key_bytes: Vec<u8>,
        value_bytes: Vec<u8>,
        fingerprint: u64,
        input_deps: &[InputDep],
        query_deps: &[QueryKey],
    ) {
        let Some(ref backend) = self.persistence else {
            return;
        };

        let (input_dep_records, query_dep_records) = {
            let name_to_id = self.name_to_id.read().expect("name_to_id lock poisoned");

            let input_dep_records: Vec<DepRecord> = input_deps
                .iter()
                .filter_map(|dep| {
                    let &id = name_to_id.get(dep.key.name)?;
                    Some(DepRecord {
                        query_id: id.0,
                        key_hash: dep.key.key.hash,
                        fingerprint: dep.fingerprint,
                    })
                })
                .collect();

            let query_dep_records: Vec<DepRecord> = {
                let cache = self.cache.read().expect("cache lock poisoned");
                query_deps
                    .iter()
                    .filter_map(|qk| {
                        let fp = cache.get(qk)?.fingerprint?;
                        let &id = name_to_id.get(qk.name)?;
                        Some(DepRecord {
                            query_id: id.0,
                            key_hash: qk.key.hash,
                            fingerprint: fp,
                        })
                    })
                    .collect()
            };

            (input_dep_records, query_dep_records)
        };

        let metadata = EntryMetadata {
            fingerprint,
            input_deps: input_dep_records,
            query_deps: query_dep_records,
        };

        let metadata_bytes = match bincode::serialize(&metadata) {
            Ok(bytes) => bytes,
            Err(e) => {
                log::warn!("failed to serialize metadata for {}: {}", Q::NAME, e);
                return;
            }
        };

        if let Err(e) = backend.stage_write(Q::ID, key_hash, key_bytes, metadata_bytes, value_bytes)
        {
            log::warn!("failed to stage write for {}: {}", Q::NAME, e);
            return;
        }

        // Insert into meta_cache so subsequent dep validation sees the new entry
        self.meta_cache
            .write()
            .expect("meta_cache lock poisoned")
            .insert((Q::ID, key_hash), metadata);
    }

    /// Try to load a query result from the persistence backend.
    ///
    /// Loads metadata, verifies the key matches (collision check),
    /// validates input and query deps, then loads the value on success.
    /// Converts persisted deps to in-memory format and inserts the result
    /// into the in-memory cache.
    ///
    /// Returns `Some(value)` on success, `None` on any failure (missing entry,
    /// deserialization error, stale deps). The caller should fall through to
    /// recomputation on `None`.
    fn try_load_persisted<Q: Query>(&self, qkey: &QueryKey, key: &Q::Key) -> Option<Q::Value> {
        let backend = self.persistence.as_ref()?;
        let cache_meta = backend.load_meta(Q::ID, qkey.key.hash).ok()??;

        // Collision check: verify the serialized key matches
        let key_bytes = bincode::serialize(key).ok()?;
        if cache_meta.key_bytes != key_bytes {
            return None;
        }

        // Deserialize the entry metadata
        let metadata: EntryMetadata = bincode::deserialize(&cache_meta.metadata_bytes).ok()?;

        // Validate input deps
        if !self.validate_persisted_input_deps(&metadata.input_deps) {
            return None;
        }

        // Validate query deps (metadata-only recursive fingerprint check)
        let mut visited = HashSet::new();
        if !self.validate_persisted_deps(&metadata.query_deps, &mut visited) {
            return None;
        }

        // Load the value (only after validation passes)
        let value_bytes = backend.load_value(Q::ID, qkey.key.hash).ok()??;
        let value: Q::Value = bincode::deserialize(&value_bytes).ok()?;

        // Insert metadata into meta_cache for dep validation of downstream queries
        self.meta_cache
            .write()
            .expect("meta_cache lock poisoned")
            .insert((Q::ID, qkey.key.hash), metadata.clone());

        // Convert persisted deps to in-memory format so future revalidation
        // uses the single unified path.
        let input_deps = self.convert_persisted_input_deps(&metadata.input_deps);
        let query_deps = self.convert_persisted_query_deps(&metadata.query_deps);

        let key_arc: Arc<dyn Any + Send + Sync> = Arc::new(key.clone());
        self.cache.write().expect("cache lock poisoned").insert(
            qkey.clone(),
            CachedValue {
                key: key_arc,
                value: Arc::new(value.clone()),
                input_deps,
                query_deps,
                validated_at: AtomicU64::new(self.revision.load(Ordering::SeqCst)),
                fingerprint: Some(metadata.fingerprint),
            },
        );

        Some(value)
    }

    /// Start profiling timer if profiling is enabled.
    fn profiling_start(&self) -> Option<Instant> {
        if self.profiling.load(Ordering::Relaxed) {
            Some(Instant::now())
        } else {
            None
        }
    }

    /// Record a profiling stat (hit or miss) for the given query.
    fn record_stat(&self, name: &'static str, call_start: Option<Instant>, hit: bool) {
        if let Some(start) = call_start {
            let elapsed = start.elapsed().as_nanos() as u64;
            let mut stats = self.stats.lock().expect("stats lock poisoned");
            let entry = stats.entry(name).or_default();
            if hit {
                entry.hits += 1;
            } else {
                entry.misses += 1;
            }
            entry.total_ns += elapsed;
        }
    }

    pub fn set_input<I: Input>(&self, key: I::Key, value: I::Value) {
        let ikey = InputKey {
            name: I::NAME,
            key: KeyId::new(&key),
        };
        self.register_input::<I>();
        self.inputs
            .write()
            .expect("inputs lock poisoned")
            .insert(ikey, Arc::new(value));
        self.revision.fetch_add(1, Ordering::SeqCst);
    }

    pub fn get_input<I: Input>(&self, key: I::Key) -> I::Value {
        let ikey = InputKey {
            name: I::NAME,
            key: KeyId::new(&key),
        };
        self.register_input::<I>();
        let inputs = self.inputs.read().expect("inputs lock poisoned");
        let value = inputs
            .get(&ikey)
            .expect("missing input")
            .downcast_ref::<I::Value>()
            .expect("input type mismatch");

        let fp = I::fingerprint(value);
        if let Some(frame) = self
            .active_inputs
            .lock()
            .expect("active_inputs lock poisoned")
            .last_mut()
        {
            if !frame.iter().any(|dep| dep.key == ikey) {
                frame.push(InputDep {
                    key: ikey,
                    fingerprint: fp,
                });
            }
        }

        value.clone()
    }

    /// Get an input value, returning the default if not set.
    ///
    /// This is useful for optional configuration inputs like `CompilerOptions`.
    pub fn get_input_or_default<I: Input>(&self, key: I::Key) -> I::Value
    where
        I::Value: Default,
    {
        let ikey = InputKey {
            name: I::NAME,
            key: KeyId::new(&key),
        };
        self.register_input::<I>();
        let inputs = self.inputs.read().expect("inputs lock poisoned");

        let value = match inputs.get(&ikey) {
            Some(v) => v
                .downcast_ref::<I::Value>()
                .expect("input type mismatch")
                .clone(),
            None => I::Value::default(),
        };

        let fp = I::fingerprint(&value);
        if let Some(frame) = self
            .active_inputs
            .lock()
            .expect("active_inputs lock poisoned")
            .last_mut()
        {
            if !frame.iter().any(|dep| dep.key == ikey) {
                frame.push(InputDep {
                    key: ikey,
                    fingerprint: fp,
                });
            }
        }

        value
    }

    fn inputs_match(&self, deps: &[InputDep]) -> bool {
        let inputs = self.inputs.read().expect("inputs lock poisoned");
        let fingerprints = self
            .input_fingerprints
            .read()
            .expect("input_fingerprints lock poisoned");
        for dep in deps {
            let current = inputs.get(&dep.key);
            let Some(current) = current else {
                return false;
            };

            let Some(fingerprint_fn) = fingerprints.get(dep.key.name) else {
                return false;
            };

            let current_fp = fingerprint_fn(current.as_ref());
            if current_fp != dep.fingerprint {
                return false;
            }
        }

        true
    }

    /// Force-validate query dependencies using the early-exit algorithm.
    /// For each dep, force-recompute via the registered recompute function
    /// and compare the new fingerprint with the stored one. If the fingerprint
    /// is unchanged, the dependent is still valid (green).
    fn force_validate_query_deps(&self, deps: &[QueryKey]) -> bool {
        for dep_key in deps {
            // Read old fingerprint and key from cache (then release lock)
            let (old_fp, key_arc) = {
                let cache = self.cache.read().expect("cache lock poisoned");
                let Some(dep_cached) = cache.get(dep_key) else {
                    return false;
                };
                let Some(old_fp) = dep_cached.fingerprint else {
                    return false;
                };
                (old_fp, dep_cached.key.clone())
            };

            // Get recompute function
            let recompute_fn = {
                let fns = self.query_fns.read().expect("query_fns lock poisoned");
                let Some(fns) = fns.get(dep_key.name) else {
                    return false;
                };
                fns.recompute
            };

            // Force-recompute: calls db.query() internally, which may
            // recompute the dep if its own deps have changed
            match recompute_fn(self, key_arc) {
                Some(new_fp) if new_fp == old_fp => continue,
                _ => return false,
            }
        }

        true
    }

    /// Look up the current fingerprint of an input by name and key hash.
    /// Used for validating persisted entries whose deps reference inputs.
    fn current_input_fingerprint(&self, name: &str, key_hash: u64) -> Option<u64> {
        let fingerprints = self
            .input_fingerprints
            .read()
            .expect("input_fingerprints lock poisoned");
        let (&static_name, &fingerprint_fn) = fingerprints.get_key_value(name)?;

        let ikey = InputKey {
            name: static_name,
            key: KeyId { hash: key_hash },
        };
        let inputs = self.inputs.read().expect("inputs lock poisoned");
        let value = inputs.get(&ikey)?;
        Some(fingerprint_fn(value.as_ref()))
    }

    /// Validate input dependencies from a persisted entry.
    fn validate_persisted_input_deps(&self, deps: &[DepRecord]) -> bool {
        let id_to_name = self.id_to_name.read().expect("id_to_name lock poisoned");
        for dep in deps {
            let Some(&name) = id_to_name.get(&QueryId(dep.query_id)) else {
                return false;
            };
            match self.current_input_fingerprint(name, dep.key_hash) {
                Some(fp) if fp == dep.fingerprint => continue,
                _ => return false,
            }
        }
        true
    }

    /// Look up a cached query's fingerprint by QueryId and key hash.
    fn find_cached_fingerprint_by_id(&self, query_id: QueryId, key_hash: u64) -> Option<u64> {
        let name = {
            let map = self.id_to_name.read().expect("id_to_name lock poisoned");
            *map.get(&query_id)?
        };
        let qkey = QueryKey {
            name,
            key: KeyId { hash: key_hash },
        };
        let cache = self.cache.read().expect("cache lock poisoned");
        cache.get(&qkey).and_then(|cv| cv.fingerprint)
    }

    /// Load entry metadata from the meta_cache or persistence backend.
    fn load_entry_metadata(&self, query_id: QueryId, key_hash: u64) -> Option<EntryMetadata> {
        // Check meta_cache first
        {
            let cache = self.meta_cache.read().expect("meta_cache lock poisoned");
            if let Some(meta) = cache.get(&(query_id, key_hash)) {
                return Some(meta.clone());
            }
        }

        // Load from backend
        let backend = self.persistence.as_ref()?;
        let cache_meta = backend.load_meta(query_id, key_hash).ok()??;
        let metadata: EntryMetadata = bincode::deserialize(&cache_meta.metadata_bytes).ok()?;

        self.meta_cache
            .write()
            .expect("meta_cache lock poisoned")
            .insert((query_id, key_hash), metadata.clone());

        Some(metadata)
    }

    /// Validate query dependencies from a persisted entry using **metadata-only**
    /// fingerprint checking — NO force-recompute, NO value deserialization.
    ///
    /// # Why metadata-only (not force-recompute)?
    ///
    /// Persisted validation happens on a fresh process start (or first access
    /// after startup). At this point, NO inputs have changed since the cache was
    /// written — we're just confirming the world hasn't changed. We can verify
    /// this by recursively checking that:
    ///
    ///   1. Each dep's stored fingerprint matches the persisted entry's fingerprint.
    ///   2. Each dep's own input deps still match the current live inputs.
    ///   3. Each dep's own query deps are recursively valid (same algorithm).
    ///
    /// This is fundamentally different from the **in-memory** early-exit path
    /// (`force_validate_query_deps`), which runs after an input has actually
    /// changed within a long-running process (e.g., LSP file edit). In that
    /// case, force-recomputing deps via `db.query()` is necessary because the
    /// output may have genuinely changed.
    ///
    /// The two paths complement each other:
    /// - **Persisted validation** (this method): confirms identity on cold start.
    ///   Metadata-only — never calls `db.query()`, never deserializes values.
    /// - **In-memory early-exit** (`force_validate_query_deps`): propagates
    ///   changes within a running process. Force-recomputes deps to compare
    ///   fingerprints.
    ///
    /// Once a persisted entry passes validation here and is loaded into the
    /// in-memory cache (by `try_load_persisted`), all subsequent revalidation
    /// uses the in-memory path — persisted validation is never revisited for
    /// that entry.
    fn validate_persisted_deps(
        &self,
        deps: &[DepRecord],
        visited: &mut HashSet<(u32, u64)>,
    ) -> bool {
        for dep in deps {
            let key = (dep.query_id, dep.key_hash);
            if !visited.insert(key) {
                // Already validated this dep in this validation walk — skip to
                // avoid infinite recursion on diamond-shaped dep graphs.
                continue;
            }

            let query_id = QueryId(dep.query_id);

            // Fast path: if this dep is already in the in-memory cache (e.g.,
            // loaded by a prior query in this session), just compare fingerprints.
            if let Some(fp) = self.find_cached_fingerprint_by_id(query_id, dep.key_hash) {
                if fp == dep.fingerprint {
                    continue;
                } else {
                    return false;
                }
            }

            // Not in memory — load the dep's metadata from meta_cache or backend.
            let Some(metadata) = self.load_entry_metadata(query_id, dep.key_hash) else {
                return false;
            };

            // Metadata-only validation:
            // 1. Check that the dep's stored fingerprint matches what we expect.
            if metadata.fingerprint != dep.fingerprint {
                return false;
            }
            // 2. Verify the dep's input deps against current live inputs.
            if !self.validate_persisted_input_deps(&metadata.input_deps) {
                return false;
            }
            // 3. Recursively validate the dep's own query deps (same algorithm).
            if !self.validate_persisted_deps(&metadata.query_deps, visited) {
                return false;
            }
        }
        true
    }

    /// Convert persisted input deps to in-memory `InputDep` format.
    ///
    /// Looks up `&'static str` names from the ID-to-name registry.
    /// Deps whose IDs aren't registered are silently dropped (shouldn't
    /// happen after successful validation).
    fn convert_persisted_input_deps(&self, deps: &[DepRecord]) -> Vec<InputDep> {
        let id_to_name = self.id_to_name.read().expect("id_to_name lock poisoned");
        deps.iter()
            .filter_map(|dep| {
                let &name = id_to_name.get(&QueryId(dep.query_id))?;
                Some(InputDep {
                    key: InputKey {
                        name,
                        key: KeyId { hash: dep.key_hash },
                    },
                    fingerprint: dep.fingerprint,
                })
            })
            .collect()
    }

    /// Convert persisted query deps to in-memory `QueryKey` format.
    ///
    /// Looks up `&'static str` names from the ID-to-name registry.
    /// Deps whose IDs aren't registered are silently dropped (shouldn't
    /// happen after successful validation).
    fn convert_persisted_query_deps(&self, deps: &[DepRecord]) -> Vec<QueryKey> {
        let id_to_name = self.id_to_name.read().expect("id_to_name lock poisoned");
        deps.iter()
            .filter_map(|dep| {
                let &name = id_to_name.get(&QueryId(dep.query_id))?;
                Some(QueryKey {
                    name,
                    key: KeyId { hash: dep.key_hash },
                })
            })
            .collect()
    }

    fn register_input<I: Input>(&self) {
        {
            let registry = self
                .input_fingerprints
                .read()
                .expect("input_fingerprints lock poisoned");
            if registry.contains_key(I::NAME) {
                return;
            }
        }

        // Collision detection and ID registration
        {
            let mut id_map = self.id_to_name.write().expect("id_to_name lock poisoned");
            if let Some(&existing) = id_map.get(&I::ID) {
                if existing != I::NAME {
                    panic!(
                        "QueryId collision: {} and {} both hash to {:?}",
                        existing,
                        I::NAME,
                        I::ID
                    );
                }
            }
            id_map.insert(I::ID, I::NAME);
        }
        self.name_to_id
            .write()
            .expect("name_to_id lock poisoned")
            .insert(I::NAME, I::ID);

        fn fingerprint_any<I: Input>(value: &dyn Any) -> u64 {
            let value = value
                .downcast_ref::<I::Value>()
                .expect("input type mismatch");
            I::fingerprint(value)
        }

        self.input_fingerprints
            .write()
            .expect("input_fingerprints lock poisoned")
            .insert(I::NAME, fingerprint_any::<I>);
    }

    /// Register type-erased recompute and key deserialization functions for query Q.
    /// Called lazily on first `db.query::<Q>()` invocation.
    fn register_recompute<Q: Query>(&self) {
        {
            let fns = self.query_fns.read().expect("query_fns lock poisoned");
            if fns.contains_key(Q::NAME) {
                return;
            }
        }

        // Collision detection and ID registration
        {
            let mut id_map = self.id_to_name.write().expect("id_to_name lock poisoned");
            if let Some(&existing) = id_map.get(&Q::ID) {
                if existing != Q::NAME {
                    panic!(
                        "QueryId collision: {} and {} both hash to {:?}",
                        existing,
                        Q::NAME,
                        Q::ID
                    );
                }
            }
            id_map.insert(Q::ID, Q::NAME);
        }
        self.name_to_id
            .write()
            .expect("name_to_id lock poisoned")
            .insert(Q::NAME, Q::ID);

        fn recompute_fn<Q: Query>(
            db: &Database,
            key_any: Arc<dyn Any + Send + Sync>,
        ) -> Option<u64> {
            let key = key_any.downcast_ref::<Q::Key>()?.clone();
            let qkey = QueryKey {
                name: Q::NAME,
                key: KeyId::new(&key),
            };
            let _ = db.query::<Q>(key);
            let cache = db.cache.read().expect("cache lock poisoned");
            cache.get(&qkey).and_then(|cv| cv.fingerprint)
        }

        self.query_fns
            .write()
            .expect("query_fns lock poisoned")
            .entry(Q::NAME)
            .or_insert(QueryFns {
                recompute: recompute_fn::<Q>,
            });
    }
}

impl KeyId {
    pub fn new<T: Hash>(key: &T) -> Self {
        let mut hasher = FnvHasher::default();
        key.hash(&mut hasher);
        Self {
            hash: hasher.finish(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FileInputKey {
    pub path: FilePath,
}

#[cfg(test)]
mod tests {
    use std::{
        hash::{Hash, Hasher},
        sync::atomic::{AtomicU64, Ordering},
    };

    use ray_query_macros::{input, query};
    use serde::{Deserialize, Serialize};

    use crate::{
        persistence::{QueryId, file_backend::FileBackend},
        query::{CyclePolicy, Database, Input, Query},
    };

    #[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
    struct IntKey(u64);

    #[allow(dead_code)]
    #[derive(Clone, Hash)]
    #[input(key = "IntKey")]
    struct IntInput(u64);

    struct ReadInt;

    impl Query for ReadInt {
        type Key = IntKey;
        type Value = u64;

        const NAME: &'static str = "ReadInt";
        const ID: QueryId = QueryId(0x1);

        fn compute(db: &Database, key: Self::Key) -> Self::Value {
            db.get_input::<IntInput>(key).0
        }
    }

    struct AddOne;

    impl Query for AddOne {
        type Key = IntKey;
        type Value = u64;

        const NAME: &'static str = "AddOne";
        const ID: QueryId = QueryId(0x2);

        fn compute(db: &Database, key: Self::Key) -> Self::Value {
            db.query::<ReadInt>(key) + 1
        }
    }

    struct CycleQuery;

    impl Query for CycleQuery {
        type Key = IntKey;
        type Value = u64;

        const NAME: &'static str = "CycleQuery";
        const ID: QueryId = QueryId(0x3);
        const CYCLE_POLICY: CyclePolicy = CyclePolicy::Error;

        fn compute(db: &Database, key: Self::Key) -> Self::Value {
            db.query::<CycleQuery>(key)
        }

        fn on_cycle(_db: &Database, _key: Self::Key) -> Self::Value {
            42
        }
    }

    #[test]
    fn input_fingerprint_invalidation() {
        let db = Database::new();
        let key = IntKey(1);

        IntInput::new(&db, key.clone(), 10);
        let first = db.query::<ReadInt>(key.clone());
        assert_eq!(first, 10);

        IntInput::new(&db, key.clone(), 11);
        let second = db.query::<ReadInt>(key.clone());
        assert_eq!(second, 11);
    }

    #[test]
    fn query_dependency_invalidation_propagates() {
        let db = Database::new();
        let key = IntKey(2);

        IntInput::new(&db, key.clone(), 5);
        let first = db.query::<AddOne>(key.clone());
        assert_eq!(first, 6);

        IntInput::new(&db, key.clone(), 9);
        let second = db.query::<AddOne>(key.clone());
        assert_eq!(second, 10);
    }

    #[test]
    fn cycle_policy_error_uses_on_cycle() {
        let db = Database::new();
        let key = IntKey(3);
        let value = db.query::<CycleQuery>(key);
        assert_eq!(value, 42);
    }

    #[query]
    fn read_int_query(db: &Database, key: IntKey) -> u64 {
        db.get_input::<IntInput>(key).0
    }

    #[query]
    fn add_one_query(db: &Database, key: IntKey) -> u64 {
        read_int_query(db, key) + 1
    }

    #[test]
    fn macro_query_uses_inputs() {
        let db = Database::new();
        let key = IntKey(4);

        IntInput::new(&db, key.clone(), 7);
        let value = read_int_query(&db, key);
        assert_eq!(value, 7);
    }

    #[test]
    fn macro_query_dependency_propagates() {
        let db = Database::new();
        let key = IntKey(5);

        IntInput::new(&db, key.clone(), 1);
        let first = add_one_query(&db, key.clone());
        assert_eq!(first, 2);

        IntInput::new(&db, key.clone(), 3);
        let second = add_one_query(&db, key);
        assert_eq!(second, 4);
    }

    #[input(fingerprint = "other_input_fingerprint")]
    fn other_input(_db: &Database, _key: IntKey) -> u64 {
        0
    }

    fn other_input_fingerprint(value: &u64) -> u64 {
        *value
    }

    #[query]
    fn read_other_query(db: &Database, key: IntKey) -> u64 {
        other_input(db, key)
    }

    #[query]
    fn no_input_query(_db: &Database, key: IntKey) -> u64 {
        key.0 + 100
    }

    #[test]
    fn input_specific_invalidations_are_isolated() {
        let db = Database::new();
        let key = IntKey(6);

        IntInput::new(&db, key.clone(), 10);
        set_other_input(&db, key.clone(), 20);

        let a1 = db.query::<ReadInt>(key.clone());
        let b1 = read_other_query(&db, key.clone());
        assert_eq!(a1, 10);
        assert_eq!(b1, 20);

        IntInput::new(&db, key.clone(), 11);
        let a2 = db.query::<ReadInt>(key.clone());
        let b2 = read_other_query(&db, key.clone());
        assert_eq!(a2, 11);
        assert_eq!(b2, 20);
    }

    #[test]
    fn queries_without_inputs_remain_cached() {
        let db = Database::new();
        let key = IntKey(7);

        let first = no_input_query(&db, key.clone());
        assert_eq!(first, 107);

        IntInput::new(&db, key.clone(), 1);
        let second = no_input_query(&db, key);
        assert_eq!(second, 107);
    }

    #[test]
    fn tuple_input_accessors_work() {
        let db = Database::new();
        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        #[input]
        struct PlainInput(u64);

        let input = PlainInput(0);

        input.set_value(&db, PlainInput(12));
        let value = input.value(&db);
        assert_eq!(value, PlainInput(12));
    }

    #[test]
    fn multi_field_input_works() {
        let db = Database::new();

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        struct MultiKey(u64);

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        #[input(key = "MultiKey")]
        struct MultiFieldInput {
            name: String,
            count: u64,
        }

        let key = MultiKey(1);
        MultiFieldInput::new(&db, key.clone(), "hello".to_string(), 42);

        let retrieved = db.get_input::<MultiFieldInput>(key);
        assert_eq!(retrieved.name, "hello");
        assert_eq!(retrieved.count, 42);
    }

    #[test]
    fn multi_field_tuple_input_works() {
        let db = Database::new();

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        struct TupleKey(u64);

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        #[input(key = "TupleKey")]
        struct MultiTupleInput(String, u64, bool);

        let key = TupleKey(1);
        MultiTupleInput::new(&db, key.clone(), "test".to_string(), 100, true);

        let retrieved = db.get_input::<MultiTupleInput>(key);
        assert_eq!(retrieved.0, "test");
        assert_eq!(retrieved.1, 100);
        assert_eq!(retrieved.2, true);
    }

    #[test]
    fn new_database_has_no_persistence() {
        let db = Database::new();
        assert!(!db.has_persistence());
    }

    #[test]
    fn with_persistence_enables_persistence() {
        let dir = tempfile::tempdir().unwrap();
        let db = Database::with_persistence(Box::new(FileBackend::new(dir.path().join("cache"))));
        assert!(db.has_persistence());
    }

    #[test]
    fn flush_persistence_noop_without_backend() {
        let db = Database::new();
        // Should succeed silently with no persistence configured
        assert!(db.flush_persistence().is_ok());
    }

    #[test]
    fn flush_persistence_delegates_to_backend() {
        let dir = tempfile::tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let db = Database::with_persistence(Box::new(FileBackend::new(cache_dir.clone())));

        // Compute a query to stage a write, then flush
        let key = IntKey(200);
        IntInput::new(&db, key.clone(), 42);
        let _ = db.query::<ReadInt>(key);
        db.flush_persistence().unwrap();

        // Verify files were written to the cache directory
        assert!(cache_dir.exists());
    }

    // --- Persistence integration tests ---

    fn new_persist_db(cache_dir: &std::path::Path) -> Database {
        Database::with_persistence(Box::new(FileBackend::new(cache_dir.to_path_buf())))
    }

    /// Helper: create a Database with persistence, set input, compute, flush.
    fn setup_persist_db(cache_dir: &std::path::Path, key: IntKey, input_value: u64) -> Database {
        let db = new_persist_db(cache_dir);
        IntInput::new(&db, key.clone(), input_value);
        let _ = db.query::<ReadInt>(key);
        db.flush_persistence().unwrap();
        db
    }

    #[test]
    fn persist_write_and_load_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let key = IntKey(100);

        // Build 1: compute and flush
        let db1 = setup_persist_db(&cache_dir, key.clone(), 42);
        assert_eq!(db1.query::<ReadInt>(key.clone()), 42);

        // Build 2: fresh database with same inputs, should load from persistence
        let db2 = new_persist_db(&cache_dir);
        IntInput::new(&db2, key.clone(), 42);
        let result = db2.query::<ReadInt>(key);
        assert_eq!(result, 42);
    }

    #[test]
    fn persist_invalidated_on_input_change() {
        let dir = tempfile::tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let key = IntKey(101);

        // Build 1: input=10
        setup_persist_db(&cache_dir, key.clone(), 10);

        // Build 2: input changed to 20 — persisted entry should be invalidated
        let db2 = new_persist_db(&cache_dir);
        IntInput::new(&db2, key.clone(), 20);
        let result = db2.query::<ReadInt>(key);
        assert_eq!(result, 20);
    }

    #[test]
    fn persist_with_query_dependencies() {
        let dir = tempfile::tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let key = IntKey(102);

        // Build 1: compute AddOne (depends on ReadInt) and flush
        let db1 = new_persist_db(&cache_dir);
        IntInput::new(&db1, key.clone(), 5);
        assert_eq!(db1.query::<AddOne>(key.clone()), 6);
        db1.flush_persistence().unwrap();

        // Build 2: same inputs — both should load from persistence
        let db2 = new_persist_db(&cache_dir);
        IntInput::new(&db2, key.clone(), 5);
        assert_eq!(db2.query::<AddOne>(key), 6);
    }

    #[test]
    fn persist_corrupted_entry_falls_back_to_compute() {
        let dir = tempfile::tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let key = IntKey(103);

        // Build 1: compute and flush
        setup_persist_db(&cache_dir, key.clone(), 99);

        // Corrupt the cache entries — ReadInt has QueryId(0x1), directory "1"
        let query_dir = cache_dir.join("1");
        for entry in std::fs::read_dir(&query_dir).unwrap() {
            let path = entry.unwrap().path();
            std::fs::write(&path, b"corrupted data").unwrap();
        }

        // Build 2: should fall back to compute despite corrupted entry
        let db2 = new_persist_db(&cache_dir);
        IntInput::new(&db2, key.clone(), 99);
        assert_eq!(db2.query::<ReadInt>(key), 99);
    }

    #[test]
    fn persist_revalidation_after_revision_bump() {
        let dir = tempfile::tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let key = IntKey(104);

        // Build 1: compute and flush
        setup_persist_db(&cache_dir, key.clone(), 50);

        // Build 2: load from persistence, then set_input with same value (bumps revision)
        let db2 = new_persist_db(&cache_dir);
        IntInput::new(&db2, key.clone(), 50);
        let first = db2.query::<ReadInt>(key.clone());
        assert_eq!(first, 50);

        // Set same input value (revision bumps but fingerprint unchanged)
        IntInput::new(&db2, key.clone(), 50);
        let second = db2.query::<ReadInt>(key);
        assert_eq!(second, 50);
    }

    #[test]
    fn early_exit_dep_unchanged_skips_recompute() {
        static COMPUTE_COUNT: AtomicU64 = AtomicU64::new(0);

        struct CountedAddOne;
        impl Query for CountedAddOne {
            type Key = IntKey;
            type Value = u64;
            const NAME: &'static str = "CountedAddOne";
            const ID: QueryId = QueryId(0x4);
            fn compute(db: &Database, key: Self::Key) -> Self::Value {
                COMPUTE_COUNT.fetch_add(1, Ordering::SeqCst);
                db.query::<ReadInt>(key) + 1
            }
        }

        // ReadInt is the dep. If the input changes but ReadInt's output is
        // the same, CountedAddOne should NOT be recomputed.
        // Since IntInput fingerprint IS the value, changing value always
        // changes ReadInt's output. So we test the early-exit path by
        // keeping the input the same after a revision bump.

        let db = Database::new();
        let key = IntKey(105);

        IntInput::new(&db, key.clone(), 10);

        COMPUTE_COUNT.store(0, Ordering::SeqCst);
        assert_eq!(db.query::<CountedAddOne>(key.clone()), 11);
        assert_eq!(COMPUTE_COUNT.load(Ordering::SeqCst), 1);

        // Set a DIFFERENT input key (bumps revision but doesn't affect our dep)
        let other_key = IntKey(999);
        IntInput::new(&db, other_key, 0);

        // CountedAddOne should NOT be recomputed (early-exit: dep fingerprint unchanged)
        assert_eq!(db.query::<CountedAddOne>(key), 11);
        assert_eq!(COMPUTE_COUNT.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn early_exit_dep_changed_triggers_recompute() {
        static RECOMPUTE_COUNT: AtomicU64 = AtomicU64::new(0);

        struct TrackedAddOne;
        impl Query for TrackedAddOne {
            type Key = IntKey;
            type Value = u64;
            const NAME: &'static str = "TrackedAddOne";
            const ID: QueryId = QueryId(0x5);
            fn compute(db: &Database, key: Self::Key) -> Self::Value {
                RECOMPUTE_COUNT.fetch_add(1, Ordering::SeqCst);
                db.query::<ReadInt>(key) + 1
            }
        }

        let db = Database::new();
        let key = IntKey(106);

        IntInput::new(&db, key.clone(), 10);

        RECOMPUTE_COUNT.store(0, Ordering::SeqCst);
        assert_eq!(db.query::<TrackedAddOne>(key.clone()), 11);
        assert_eq!(RECOMPUTE_COUNT.load(Ordering::SeqCst), 1);

        // Change the input — dep fingerprint WILL change
        IntInput::new(&db, key.clone(), 20);
        assert_eq!(db.query::<TrackedAddOne>(key), 21);
        assert_eq!(RECOMPUTE_COUNT.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn persist_loaded_entry_revalidates_after_input_change() {
        let dir = tempfile::tempdir().unwrap();
        let cache_dir = dir.path().join("cache");
        let key = IntKey(107);

        // Build 1: compute AddOne chain and flush
        let db1 = new_persist_db(&cache_dir);
        IntInput::new(&db1, key.clone(), 5);
        assert_eq!(db1.query::<AddOne>(key.clone()), 6);
        db1.flush_persistence().unwrap();

        // Build 2: different input — persisted entries should be invalidated
        let db2 = new_persist_db(&cache_dir);
        IntInput::new(&db2, key.clone(), 15);
        assert_eq!(db2.query::<AddOne>(key), 16);
    }
}
