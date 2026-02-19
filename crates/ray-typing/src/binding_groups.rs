// Binding group construction for the type system.
// SCC-based grouping is used to group mutually recursive bindings.
// Callers may now compute SCCs over a *filtered* set of bindings
// (e.g., just top-level bindings), and use separate ownership indices
// for locals. This file still provides SCC grouping, but callers
// can induce subgraphs for custom grouping needs.

use std::collections::{BTreeSet, HashMap};
use std::ops::{Deref, DerefMut};

use ray_shared::graph::DirectedGraph;
use serde::{Deserialize, Serialize};

// Represents a single binding in a module or scope.
// The concrete shape will depend on the frontend AST.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct BindingId(pub u64);

impl std::fmt::Display for BindingId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "b{}", self.0)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(serialize = "T: Serialize", deserialize = "T: Deserialize<'de>"))]
pub struct BindingGroup<T> {
    pub bindings: Vec<T>,
}

impl<T> BindingGroup<T> {
    pub fn new(bindings: Vec<T>) -> Self {
        BindingGroup { bindings }
    }
}

impl<T: std::fmt::Display> std::fmt::Display for BindingGroup<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let parts = self
            .bindings
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "BindingGroup[{}]", parts)
    }
}

/// A dependency graph between bindings, backed by `DirectedGraph<T>`.
///
/// An edge `from -> to` means that the definition of `from` refers to `to`.
/// Provides binding-specific methods (topo-sorted SCCs) on top of the
/// generic graph operations available via `Deref<Target = DirectedGraph<T>>`.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(
    serialize = "T: Serialize + Ord",
    deserialize = "T: Deserialize<'de> + Ord"
))]
pub struct BindingGraph<T>(pub DirectedGraph<T>);

impl<T> Deref for BindingGraph<T> {
    type Target = DirectedGraph<T>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for BindingGraph<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Clone + Eq + std::hash::Hash + Ord> BindingGraph<T> {
    pub fn new() -> Self {
        BindingGraph(DirectedGraph::new())
    }

    /// Add a binding (node) with no outgoing edges.
    pub fn add_binding(&mut self, id: T) {
        self.0.add_node(id);
    }

    /// Returns a new `BindingGraph` induced by the set of nodes.
    /// Only bindings in `nodes` are included as keys in the new graph,
    /// and only edges where both endpoints are in `nodes` are kept.
    pub fn induced_subgraph(&self, nodes: &BTreeSet<T>) -> BindingGraph<T> {
        BindingGraph(self.0.induced_subgraph(nodes))
    }

    /// Compute binding groups as strongly connected components (SCCs) of the
    /// dependency graph, topologically sorted so that dependencies come before
    /// dependents.
    pub fn compute_binding_groups(&self) -> Vec<BindingGroup<T>> {
        let sccs = self.0.compute_sccs();

        // Build a condensation graph of SCCs and compute a topo order where
        // dependencies come before dependents.
        let comp_count = sccs.len();
        let mut comp_index_of: HashMap<T, usize> = HashMap::new();
        for (ci, comp) in sccs.iter().enumerate() {
            for bid in comp {
                comp_index_of.insert(bid.clone(), ci);
            }
        }

        let mut comp_edges: Vec<Vec<usize>> = vec![Vec::new(); comp_count];
        let mut indegree: Vec<usize> = vec![0; comp_count];
        for (from, neighbours) in &self.0.edges {
            if let Some(&from_ci) = comp_index_of.get(from) {
                for to in neighbours {
                    if let Some(&to_ci) = comp_index_of.get(to) {
                        if from_ci != to_ci {
                            // Edge from dependency to dependent so that
                            // dependencies appear earlier in topological order.
                            if !comp_edges[to_ci].contains(&from_ci) {
                                comp_edges[to_ci].push(from_ci);
                                indegree[from_ci] += 1;
                            }
                        }
                    }
                }
            }
        }

        // Kahn's algorithm for topological sort over components.
        let mut queue: Vec<usize> = (0..comp_count).filter(|&ci| indegree[ci] == 0).collect();
        let mut ordered_components: Vec<usize> = Vec::new();

        while let Some(ci) = queue.pop() {
            ordered_components.push(ci);
            for &pred in &comp_edges[ci] {
                indegree[pred] -= 1;
                if indegree[pred] == 0 {
                    queue.push(pred);
                }
            }
        }

        // Map components back to binding groups in the chosen order.
        ordered_components
            .into_iter()
            .map(|ci| BindingGroup::new(sccs[ci].clone()))
            .collect()
    }

    /// Computes binding groups (SCCs) over a filtered set of bindings.
    pub fn compute_binding_groups_over(&self, nodes: &BTreeSet<T>) -> Vec<BindingGroup<T>> {
        self.induced_subgraph(nodes).compute_binding_groups()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::binding_groups::{BindingGraph, BindingGroup, BindingId};

    fn bid(n: u64) -> BindingId {
        BindingId(n)
    }

    #[test]
    fn scc_filtered_to_subset_excludes_other_nodes() {
        // Graph: 1 <-> 2 (mutual), 3 -> 4 (no cycle)
        let mut g = BindingGraph::new();
        g.add_edge(bid(1), bid(2));
        g.add_edge(bid(2), bid(1));
        g.add_edge(bid(3), bid(4));
        // Induce on {1,2,3}
        let mut set = BTreeSet::new();
        set.insert(bid(1));
        set.insert(bid(2));
        set.insert(bid(3));
        let groups = g.compute_binding_groups_over(&set);
        // 1 and 2 should be grouped together, 3 alone, 4 not present
        let sets = group_set(&groups);
        assert_eq!(sets.len(), 2);
        assert!(sets.contains(&vec![bid(1), bid(2)]));
        assert!(sets.contains(&vec![bid(3)]));
        // 4 is not present in any group
        for g in &groups {
            assert!(!g.bindings.contains(&bid(4)));
        }
    }

    #[test]
    fn induced_subgraph_keeps_isolated_nodes() {
        // Graph: 1 (no edges), 2 -> 3
        let mut g = BindingGraph::new();
        g.add_binding(bid(1));
        g.add_edge(bid(2), bid(3));
        let mut set = BTreeSet::new();
        set.insert(bid(1));
        set.insert(bid(3));
        let sub = g.induced_subgraph(&set);
        // Should contain keys for 1 and 3, regardless of edges
        assert!(sub.edges.contains_key(&bid(1)));
        assert!(sub.edges.contains_key(&bid(3)));
        // 2 should not appear
        assert!(!sub.edges.contains_key(&bid(2)));
    }

    fn group_index_of(groups: &[BindingGroup<BindingId>], b: BindingId) -> usize {
        groups
            .iter()
            .position(|g| g.bindings.contains(&b))
            .unwrap_or_else(|| panic!("binding {b} not found in any group"))
    }

    fn group_set(groups: &[BindingGroup<BindingId>]) -> Vec<Vec<BindingId>> {
        let mut out: Vec<Vec<BindingId>> = groups
            .iter()
            .map(|g| {
                let mut v = g.bindings.clone();
                v.sort();
                v
            })
            .collect();
        out.sort();
        out
    }

    #[test]
    fn scc_single_node_no_edges() {
        let mut g = BindingGraph::new();
        g.add_binding(bid(1));

        let groups = g.compute_binding_groups();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].bindings, vec![bid(1)]);
    }

    #[test]
    fn scc_mutual_recursion_two_nodes() {
        let mut g = BindingGraph::new();
        g.add_edge(bid(1), bid(2));
        g.add_edge(bid(2), bid(1));

        let groups = g.compute_binding_groups();
        assert_eq!(groups.len(), 1);

        let mut bindings = groups[0].bindings.clone();
        bindings.sort();
        assert_eq!(bindings, vec![bid(1), bid(2)]);
    }

    #[test]
    fn scc_self_cycle_still_single_group() {
        let mut g = BindingGraph::new();
        g.add_edge(bid(1), bid(1));

        let groups = g.compute_binding_groups();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].bindings, vec![bid(1)]);
    }

    #[test]
    fn topo_order_dependencies_come_before_dependents() {
        // 1 depends on 2, and 2 depends on 3.
        // Expected: group(3) before group(2) before group(1).
        let mut g = BindingGraph::new();
        g.add_edge(bid(1), bid(2));
        g.add_edge(bid(2), bid(3));

        let groups = g.compute_binding_groups();

        let i1 = group_index_of(&groups, bid(1));
        let i2 = group_index_of(&groups, bid(2));
        let i3 = group_index_of(&groups, bid(3));

        assert!(i3 < i2, "expected 3 before 2, got {i3} and {i2}");
        assert!(i2 < i1, "expected 2 before 1, got {i2} and {i1}");

        // General property: for every edge A -> B, group(B) must not come after group(A)
        // unless A and B are in the same SCC.
        for (&from, tos) in &g.edges {
            for &to in tos {
                let ifrom = group_index_of(&groups, from);
                let ito = group_index_of(&groups, to);
                if ifrom != ito {
                    assert!(
                        ito < ifrom,
                        "expected dependency {to} to be ordered before dependent {from}; got {ito} and {ifrom}"
                    );
                }
            }
        }
    }

    #[test]
    fn topo_order_respects_sccs() {
        // SCC {1,2} depends on 3.
        let mut g = BindingGraph::new();
        g.add_edge(bid(1), bid(2));
        g.add_edge(bid(2), bid(1));
        g.add_edge(bid(1), bid(3));

        let groups = g.compute_binding_groups();
        assert_eq!(groups.len(), 2);

        let sets = group_set(&groups);
        assert_eq!(sets, vec![vec![bid(1), bid(2)], vec![bid(3)]]);

        let i12 = group_index_of(&groups, bid(1));
        let i3 = group_index_of(&groups, bid(3));
        assert!(i3 < i12, "expected 3's group before SCC(1,2)");
    }
}
