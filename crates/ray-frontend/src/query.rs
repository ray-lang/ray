use std::{
    any::Any,
    any::TypeId,
    collections::{HashMap, HashSet},
    hash::Hash,
    hash::Hasher,
    sync::{Arc, Mutex, RwLock},
};

use ray_shared::pathlib::FilePath;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum CyclePolicy {
    Panic,
    Error,
}

pub trait Query {
    type Key: Clone + Eq + Hash + Send + Sync + 'static;
    type Value: Clone + Send + Sync + 'static;

    const NAME: &'static str;
    const CYCLE_POLICY: CyclePolicy = CyclePolicy::Panic;

    fn compute(db: &Database, key: Self::Key) -> Self::Value;

    fn on_cycle(_db: &Database, _key: Self::Key) -> Self::Value {
        panic!("cycle detected in query {}", Self::NAME);
    }
}

pub trait Input {
    type Key: Clone + Eq + Hash + Send + Sync + 'static;
    type Value: Clone + Send + Sync + 'static;

    const NAME: &'static str;

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
    pub value_type: TypeId,
}

pub struct CachedValue {
    pub value: Arc<dyn Any + Send + Sync>,
    pub input_deps: Vec<InputDep>,
    pub query_deps: Vec<QueryKey>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KeyId {
    pub type_id: TypeId,
    pub hash: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct InputRegistryKey {
    pub name: &'static str,
    pub value_type: TypeId,
}

pub struct Database {
    cache: RwLock<HashMap<QueryKey, CachedValue>>,
    inputs: RwLock<HashMap<InputKey, Arc<dyn Any + Send + Sync>>>,
    input_fingerprints: RwLock<HashMap<InputRegistryKey, fn(&dyn Any) -> u64>>,
    active_stack: Mutex<Vec<QueryKey>>,
    active_inputs: Mutex<Vec<Vec<InputDep>>>,
    active_query_deps: Mutex<Vec<Vec<QueryKey>>>,
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
        }
    }

    pub fn query<Q: Query>(&self, key: Q::Key) -> Q::Value {
        let qkey = QueryKey {
            name: Q::NAME,
            key: KeyId::new(&key),
        };

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

        if let Some(cached) = self.cache.read().expect("cache lock poisoned").get(&qkey) {
            if self.cached_valid(&qkey, cached) {
                if let Some(parent_deps) = self
                    .active_query_deps
                    .lock()
                    .expect("active_query_deps lock poisoned")
                    .last_mut()
                {
                    if !parent_deps.contains(&qkey) {
                        parent_deps.push(qkey.clone());
                    }
                }

                return cached
                    .value
                    .downcast_ref::<Q::Value>()
                    .expect("type mismatch in query cache")
                    .clone();
            }
        }

        if let Some(parent_deps) = self
            .active_query_deps
            .lock()
            .expect("active_query_deps lock poisoned")
            .last_mut()
        {
            if !parent_deps.contains(&qkey) {
                parent_deps.push(qkey.clone());
            }
        }

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

        let value = Q::compute(self, key);

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

        self.cache.write().expect("cache lock poisoned").insert(
            qkey,
            CachedValue {
                value: Arc::new(value.clone()),
                input_deps,
                query_deps,
            },
        );

        value
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
                    value_type: TypeId::of::<I::Value>(),
                });
            }
        }

        value.clone()
    }

    fn cached_valid(&self, key: &QueryKey, cached: &CachedValue) -> bool {
        self.inputs_match(&cached.input_deps) && self.query_deps_match(key, &cached.query_deps)
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

            let registry_key = InputRegistryKey {
                name: dep.key.name,
                value_type: dep.value_type,
            };
            let Some(fingerprint_fn) = fingerprints.get(&registry_key) else {
                return false;
            };

            let current_fp = fingerprint_fn(current.as_ref());
            if current_fp != dep.fingerprint {
                return false;
            }
        }

        true
    }

    fn query_deps_match(&self, key: &QueryKey, deps: &[QueryKey]) -> bool {
        let mut visited = HashSet::new();
        visited.insert(key.clone());
        self.query_deps_match_with_visited(deps, &mut visited)
    }

    fn query_deps_match_with_visited(
        &self,
        deps: &[QueryKey],
        visited: &mut HashSet<QueryKey>,
    ) -> bool {
        let cache = self.cache.read().expect("cache lock poisoned");
        for dep_key in deps {
            if !visited.insert(dep_key.clone()) {
                continue;
            }

            let Some(dep_cached) = cache.get(dep_key) else {
                return false;
            };

            if !self.inputs_match(&dep_cached.input_deps) {
                return false;
            }

            if !self.query_deps_match_with_visited(&dep_cached.query_deps, visited) {
                return false;
            }
        }

        true
    }

    fn register_input<I: Input>(&self) {
        let mut registry = self
            .input_fingerprints
            .write()
            .expect("input_fingerprints lock poisoned");
        let registry_key = InputRegistryKey {
            name: I::NAME,
            value_type: TypeId::of::<I::Value>(),
        };
        if registry.contains_key(&registry_key) {
            return;
        }

        fn fingerprint_any<I: Input>(value: &dyn Any) -> u64 {
            let value = value
                .downcast_ref::<I::Value>()
                .expect("input type mismatch");
            I::fingerprint(value)
        }

        registry.insert(registry_key, fingerprint_any::<I>);
    }
}

impl KeyId {
    pub fn new<T: Hash + 'static>(key: &T) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        Self {
            type_id: TypeId::of::<T>(),
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
    use super::*;
    use ray_query_macros::{input, query};

    #[derive(Clone, Debug, Eq, PartialEq, Hash)]
    struct IntKey(u64);

    #[allow(dead_code)]
    #[input(key = "IntKey")]
    struct IntInput(u64);

    struct ReadInt;

    impl Query for ReadInt {
        type Key = IntKey;
        type Value = u64;

        const NAME: &'static str = "ReadInt";

        fn compute(db: &Database, key: Self::Key) -> Self::Value {
            db.get_input::<IntInput>(key)
        }
    }

    struct AddOne;

    impl Query for AddOne {
        type Key = IntKey;
        type Value = u64;

        const NAME: &'static str = "AddOne";

        fn compute(db: &Database, key: Self::Key) -> Self::Value {
            db.query::<ReadInt>(key) + 1
        }
    }

    struct CycleQuery;

    impl Query for CycleQuery {
        type Key = IntKey;
        type Value = u64;

        const NAME: &'static str = "CycleQuery";
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
        db.get_input::<IntInput>(key)
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

        input.set_value(&db, 12);
        let value = input.value(&db);
        assert_eq!(value, 12);
    }
}
