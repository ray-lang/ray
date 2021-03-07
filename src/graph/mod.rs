use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    hash::Hash,
};

pub trait TopologicalSort {
    type Item;

    fn peek(&self) -> Option<&Self::Item>;
    fn pop(&mut self) -> Option<Self::Item>;
    fn toposort(&mut self) -> Vec<Self::Item>;
}

#[derive(Debug, Clone)]
pub struct Dependency<V> {
    num_prec: usize,
    succ: HashSet<V>,
}

impl<V: Hash + Eq> Dependency<V> {
    fn new() -> Self {
        Self {
            num_prec: 0,
            succ: HashSet::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Graph<V, E> {
    map: HashMap<V, Dependency<V>>,
    edges: HashMap<(V, V), E>,
}

impl<V: Hash + Eq + Clone, E> Graph<V, E> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            edges: HashMap::new(),
        }
    }

    pub fn add_edge<P, S>(&mut self, prec: P, succ: S, value: Option<E>)
    where
        P: Into<V>,
        S: Into<V>,
    {
        let prec = prec.into();
        let succ = succ.into();

        if let Some(value) = value {
            self.edges.insert((prec.clone(), succ.clone()), value);
        }

        match self.map.entry(prec) {
            Entry::Vacant(e) => {
                let mut dep = Dependency::new();
                let _ = dep.succ.insert(succ.clone());
                let _ = e.insert(dep);
            }
            Entry::Occupied(e) => {
                if !e.into_mut().succ.insert(succ.clone()) {
                    // Already registered
                    return;
                }
            }
        }

        match self.map.entry(succ) {
            Entry::Vacant(e) => {
                let mut dep = Dependency::new();
                dep.num_prec += 1;
                let _ = e.insert(dep);
            }
            Entry::Occupied(e) => {
                e.into_mut().num_prec += 1;
            }
        }
    }

    fn remove(&mut self, prec: &V) -> Option<Dependency<V>> {
        let result = self.map.remove(prec);
        if let Some(ref p) = result {
            for s in &p.succ {
                if let Some(y) = self.map.get_mut(s) {
                    y.num_prec -= 1;
                }

                self.edges.remove(&(prec.clone(), s.clone()));
            }
        }
        result
    }

    pub fn strictly_dominates(&self, value: &V) -> HashSet<&V> {
        self.map
            .get(value)
            .map(|deps| deps.succ.iter().collect())
            .unwrap_or_default()
    }

    pub fn dominates(&self, value: &V) -> HashSet<&V> {
        let mut set = HashSet::new();
        for v in self.strictly_dominates(value) {
            if !set.contains(v) {
                set.insert(v);
                set.extend(self.dominates(v));
            }
        }
        set
    }
}

impl<V: Hash + Eq + Clone, E> TopologicalSort for Graph<V, E> {
    type Item = V;

    /// Return a reference to the first item that does not depend on any other items, or `None` if
    /// there is no such item.
    fn peek(&self) -> Option<&V> {
        self.map
            .iter()
            .filter(|&(_, v)| v.num_prec == 0)
            .map(|(k, _)| k)
            .next()
    }

    /// Removes the item that is not depended on by any other items and returns it, or `None` if
    /// there is no such item.
    ///
    /// If `pop` returns `None` and `len` is not 0, there is cyclic dependencies.
    fn pop(&mut self) -> Option<V> {
        self.peek().map(V::clone).map(|key| {
            let _ = self.remove(&key);
            key
        })
    }

    fn toposort(&mut self) -> Vec<Self::Item> {
        let mut v = vec![];
        while let Some(el) = self.pop() {
            v.push(el)
        }
        v
    }
}
