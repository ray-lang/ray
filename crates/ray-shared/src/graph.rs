//! Generic directed graph with Tarjan's SCC algorithm.
//!
//! Extracted from `ray-typing`'s binding groups to be reusable across crates
//! (e.g., for strong-reference cycle detection in type graphs).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use serde::{Deserialize, Serialize};

/// A directed graph with nodes of type `T` and adjacency-list edges.
///
/// An edge `from -> to` means that `from` depends on or references `to`.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(
    serialize = "T: Serialize + Ord",
    deserialize = "T: Deserialize<'de> + Ord"
))]
pub struct DirectedGraph<T> {
    pub edges: BTreeMap<T, Vec<T>>,
}

impl<T: Clone + Eq + std::hash::Hash + Ord> DirectedGraph<T> {
    pub fn new() -> Self {
        DirectedGraph {
            edges: BTreeMap::new(),
        }
    }

    /// Add a node with no outgoing edges (if it doesn't already exist).
    pub fn add_node(&mut self, id: T) {
        self.edges.entry(id).or_insert_with(Vec::new);
    }

    /// Add a directed edge from `from` to `to`, ensuring both nodes exist.
    pub fn add_edge(&mut self, from: T, to: T) {
        self.edges
            .entry(from)
            .or_insert_with(Vec::new)
            .push(to.clone());
        self.edges.entry(to).or_insert_with(Vec::new);
    }

    /// Compute the strongly connected components of this graph using
    /// Tarjan's algorithm. Returns all SCCs (including singletons).
    pub fn compute_sccs(&self) -> Vec<Vec<T>> {
        let builder = SccBuilder::new(self);
        builder.run()
    }

    /// Returns a new graph induced by the given set of nodes.
    /// Only nodes in `nodes` are included, and only edges where both
    /// endpoints are in `nodes` are kept.
    pub fn induced_subgraph(&self, nodes: &BTreeSet<T>) -> DirectedGraph<T> {
        let mut edges = BTreeMap::new();
        for id in nodes {
            let filtered: Vec<T> = self
                .edges
                .get(id)
                .map(|neighs| {
                    neighs
                        .iter()
                        .filter(|n| nodes.contains(n))
                        .cloned()
                        .collect()
                })
                .unwrap_or_else(Vec::new);
            edges.insert(id.clone(), filtered);
        }
        DirectedGraph { edges }
    }
}

/// Tarjan's SCC algorithm, parameterized over any node type `T`.
struct SccBuilder<'a, T> {
    graph: &'a DirectedGraph<T>,
    nodes: Vec<T>,
    id_to_idx: HashMap<T, usize>,
    index: usize,
    indices: Vec<Option<usize>>,
    lowlink: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    sccs: Vec<Vec<T>>,
}

impl<'a, T: Clone + Eq + std::hash::Hash + Ord> SccBuilder<'a, T> {
    fn new(graph: &'a DirectedGraph<T>) -> Self {
        let mut nodes = Vec::new();
        let mut id_to_idx = HashMap::new();

        for (id, neighbours) in &graph.edges {
            if !id_to_idx.contains_key(id) {
                let idx = nodes.len();
                nodes.push(id.clone());
                id_to_idx.insert(id.clone(), idx);
            }
            for n in neighbours {
                if !id_to_idx.contains_key(n) {
                    let idx = nodes.len();
                    nodes.push(n.clone());
                    id_to_idx.insert(n.clone(), idx);
                }
            }
        }

        let n = nodes.len();
        SccBuilder {
            graph,
            nodes,
            id_to_idx,
            index: 0,
            indices: vec![None; n],
            lowlink: vec![0; n],
            on_stack: vec![false; n],
            stack: Vec::new(),
            sccs: Vec::new(),
        }
    }

    fn strong_connect(&mut self, v: usize) {
        self.indices[v] = Some(self.index);
        self.lowlink[v] = self.index;
        self.index += 1;
        self.stack.push(v);
        self.on_stack[v] = true;

        let v_id = self.nodes[v].clone();
        if let Some(neighbours) = self.graph.edges.get(&v_id) {
            for w_id in neighbours {
                if let Some(&w) = self.id_to_idx.get(w_id) {
                    if self.indices[w].is_none() {
                        self.strong_connect(w);
                        self.lowlink[v] = self.lowlink[v].min(self.lowlink[w]);
                    } else if self.on_stack[w] {
                        if let Some(idx_w) = self.indices[w] {
                            self.lowlink[v] = self.lowlink[v].min(idx_w);
                        }
                    }
                }
            }
        }

        if let Some(idx_v) = self.indices[v] {
            if self.lowlink[v] == idx_v {
                let mut component = Vec::new();
                while let Some(w) = self.stack.pop() {
                    self.on_stack[w] = false;
                    component.push(self.nodes[w].clone());
                    if w == v {
                        break;
                    }
                }
                self.sccs.push(component);
            }
        }
    }

    fn run(mut self) -> Vec<Vec<T>> {
        for v in 0..self.nodes.len() {
            if self.indices[v].is_none() {
                self.strong_connect(v);
            }
        }
        self.sccs
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::graph::DirectedGraph;

    #[test]
    fn scc_single_node_no_edges() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        g.add_node(1);

        let sccs = g.compute_sccs();
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], vec![1]);
    }

    #[test]
    fn scc_mutual_recursion_two_nodes() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        g.add_edge(1, 2);
        g.add_edge(2, 1);

        let sccs = g.compute_sccs();
        assert_eq!(sccs.len(), 1);

        let mut bindings = sccs[0].clone();
        bindings.sort();
        assert_eq!(bindings, vec![1, 2]);
    }

    #[test]
    fn scc_self_cycle() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        g.add_edge(1, 1);

        let sccs = g.compute_sccs();
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], vec![1]);
    }

    #[test]
    fn scc_chain_no_cycle() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        g.add_edge(1, 2);
        g.add_edge(2, 3);

        let sccs = g.compute_sccs();
        // Three singletons (no cycles)
        assert_eq!(sccs.len(), 3);
        for scc in &sccs {
            assert_eq!(scc.len(), 1);
        }
    }

    #[test]
    fn scc_triangle_cycle() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 1);

        let sccs = g.compute_sccs();
        assert_eq!(sccs.len(), 1);

        let mut members = sccs[0].clone();
        members.sort();
        assert_eq!(members, vec![1, 2, 3]);
    }

    #[test]
    fn scc_multiple_independent_cycles() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        // Cycle 1: 1 <-> 2
        g.add_edge(1, 2);
        g.add_edge(2, 1);
        // Cycle 2: 3 <-> 4
        g.add_edge(3, 4);
        g.add_edge(4, 3);

        let sccs = g.compute_sccs();
        assert_eq!(sccs.len(), 2);

        let mut all: Vec<Vec<u64>> = sccs
            .into_iter()
            .map(|mut s| {
                s.sort();
                s
            })
            .collect();
        all.sort();
        assert_eq!(all, vec![vec![1, 2], vec![3, 4]]);
    }

    #[test]
    fn scc_with_string_nodes() {
        // Verifies that the graph works with non-Copy types (String is Clone but not Copy)
        let mut g: DirectedGraph<String> = DirectedGraph::new();
        g.add_edge("Foo".to_string(), "Bar".to_string());
        g.add_edge("Bar".to_string(), "Foo".to_string());

        let sccs = g.compute_sccs();
        assert_eq!(sccs.len(), 1);

        let mut members = sccs[0].clone();
        members.sort();
        assert_eq!(members, vec!["Bar".to_string(), "Foo".to_string()]);
    }

    #[test]
    fn induced_subgraph_keeps_only_specified_nodes() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        g.add_node(1);
        g.add_edge(2, 3);

        let mut set = BTreeSet::new();
        set.insert(1);
        set.insert(3);
        let sub = g.induced_subgraph(&set);

        assert!(sub.edges.contains_key(&1));
        assert!(sub.edges.contains_key(&3));
        assert!(!sub.edges.contains_key(&2));
    }

    #[test]
    fn scc_filtered_to_subset() {
        let mut g: DirectedGraph<u64> = DirectedGraph::new();
        g.add_edge(1, 2);
        g.add_edge(2, 1);
        g.add_edge(3, 4);

        let mut set = BTreeSet::new();
        set.insert(1);
        set.insert(2);
        set.insert(3);

        let sub = g.induced_subgraph(&set);
        let sccs = sub.compute_sccs();

        // {1, 2} form a cycle, {3} is a singleton
        let mut all: Vec<Vec<u64>> = sccs
            .into_iter()
            .map(|mut s| {
                s.sort();
                s
            })
            .collect();
        all.sort();
        assert_eq!(all, vec![vec![1, 2], vec![3]]);
    }
}
