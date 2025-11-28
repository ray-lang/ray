// Binding group construction for the type system.
// SCC-based grouping is used to group mutually recursive bindings.
// Callers may now compute SCCs over a *filtered* set of bindings
// (e.g., just top-level bindings), and use separate ownership indices
// for locals. This file still provides SCC grouping, but callers
// can induce subgraphs for custom grouping needs.

use std::collections::{BTreeMap, BTreeSet, HashMap};

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

#[derive(Clone, Debug)]
pub struct BindingGroup {
    pub bindings: Vec<BindingId>,
}

impl BindingGroup {
    pub fn new(bindings: Vec<BindingId>) -> Self {
        BindingGroup { bindings }
    }
}

impl std::fmt::Display for BindingGroup {
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

/// A dependency graph between bindings. An edge `from -> to` means that the
/// definition of `from` refers to `to`.
#[derive(Clone, Debug)]
pub struct BindingGraph {
    pub edges: BTreeMap<BindingId, Vec<BindingId>>,
}

struct SccBuilder<'a> {
    /// Reference to the binding dependency graph we are analyzing.
    graph: &'a BindingGraph,
    /// All binding IDs participating in the graph, each assigned a compact
    /// index for use in Tarjan's algorithm.
    nodes: Vec<BindingId>,
    /// Mapping from `BindingId` to its index in `nodes`.
    id_to_idx: HashMap<BindingId, usize>,
    /// Next depth-first search index to assign.
    index: usize,
    /// DFS discovery index for each node, or `None` if not yet visited.
    indices: Vec<Option<usize>>,
    /// Lowest index reachable from each node via DFS (Tarjan lowlink).
    lowlink: Vec<usize>,
    /// Whether a node is currently on the SCC stack.
    on_stack: Vec<bool>,
    /// Stack of node indices representing the current DFS path.
    stack: Vec<usize>,
    /// Accumulated strongly connected components as lists of `BindingId`s.
    sccs: Vec<Vec<BindingId>>,
}

impl<'a> SccBuilder<'a> {
    fn new(graph: &'a BindingGraph) -> Self {
        let mut nodes = Vec::new();
        let mut id_to_idx = HashMap::new();

        for (&id, neighbours) in &graph.edges {
            if !id_to_idx.contains_key(&id) {
                let idx = nodes.len();
                nodes.push(id);
                id_to_idx.insert(id, idx);
            }
            for &n in neighbours {
                if !id_to_idx.contains_key(&n) {
                    let idx = nodes.len();
                    nodes.push(n);
                    id_to_idx.insert(n, idx);
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
        // Set the depth index for v to the smallest unused index and push it
        // onto the stack.
        self.indices[v] = Some(self.index);
        self.lowlink[v] = self.index;
        self.index += 1;
        self.stack.push(v);
        self.on_stack[v] = true;

        let v_id = self.nodes[v];
        if let Some(neighbours) = self.graph.edges.get(&v_id) {
            for &w_id in neighbours {
                if let Some(&w) = self.id_to_idx.get(&w_id) {
                    if self.indices[w].is_none() {
                        // Successor w has not yet been visited; recurse on it.
                        self.strong_connect(w);
                        // After recursion, update v's lowlink based on w.
                        self.lowlink[v] = self.lowlink[v].min(self.lowlink[w]);
                    } else if self.on_stack[w] {
                        // Successor w is in the current SCC stack; update
                        // lowlink[v] based on w's index.
                        if let Some(idx_w) = self.indices[w] {
                            self.lowlink[v] = self.lowlink[v].min(idx_w);
                        }
                    }
                }
            }
        }

        if let Some(idx_v) = self.indices[v] {
            if self.lowlink[v] == idx_v {
                // If v is a root node, pop the stack and generate an SCC.
                let mut component = Vec::new();
                while let Some(w) = self.stack.pop() {
                    self.on_stack[w] = false;
                    component.push(self.nodes[w]);
                    if w == v {
                        break;
                    }
                }
                self.sccs.push(component);
            }
        }
    }

    fn run(mut self) -> Vec<Vec<BindingId>> {
        for v in 0..self.nodes.len() {
            if self.indices[v].is_none() {
                self.strong_connect(v);
            }
        }
        self.sccs
    }
}

impl BindingGraph {
    pub fn new() -> Self {
        BindingGraph {
            edges: BTreeMap::new(),
        }
    }

    pub fn add_binding(&mut self, id: BindingId) {
        self.edges.entry(id).or_insert_with(Vec::new);
    }

    pub fn add_edge(&mut self, from: BindingId, to: BindingId) {
        self.edges.entry(from).or_insert_with(Vec::new).push(to);
        self.edges.entry(to).or_insert_with(Vec::new);
    }

    /// Compute binding groups as strongly connected components (SCCs) of the
    /// dependency graph, as described in the type system spec.
    pub fn compute_binding_groups(&self) -> Vec<BindingGroup> {
        let builder = SccBuilder::new(self);
        let sccs = builder.run();

        // Build a condensation graph of SCCs and compute a topo order where
        // dependencies come before dependents.
        let comp_count = sccs.len();
        let mut comp_index_of: HashMap<BindingId, usize> = HashMap::new();
        for (ci, comp) in sccs.iter().enumerate() {
            for &bid in comp {
                comp_index_of.insert(bid, ci);
            }
        }

        let mut comp_edges: Vec<Vec<usize>> = vec![Vec::new(); comp_count];
        let mut indegree: Vec<usize> = vec![0; comp_count];
        for (&from, neighbours) in &self.edges {
            if let Some(&from_ci) = comp_index_of.get(&from) {
                for &to in neighbours {
                    if let Some(&to_ci) = comp_index_of.get(&to) {
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

    /// Returns a new BindingGraph induced by the set of nodes.
    /// Only bindings in `nodes` are included as keys in the new graph,
    /// and only edges where both endpoints are in `nodes` are kept.
    pub fn induced_subgraph(&self, nodes: &BTreeSet<BindingId>) -> BindingGraph {
        let mut edges = BTreeMap::new();
        for &id in nodes {
            let filtered: Vec<BindingId> = self
                .edges
                .get(&id)
                .map(|neighs| {
                    neighs
                        .iter()
                        .cloned()
                        .filter(|n| nodes.contains(n))
                        .collect()
                })
                .unwrap_or_else(Vec::new);
            edges.insert(id, filtered);
        }
        BindingGraph { edges }
    }

    /// Computes binding groups (SCCs) over a filtered set of bindings.
    pub fn compute_binding_groups_over(&self, nodes: &BTreeSet<BindingId>) -> Vec<BindingGroup> {
        self.induced_subgraph(nodes).compute_binding_groups()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    fn group_index_of(groups: &[BindingGroup], b: BindingId) -> usize {
        groups
            .iter()
            .position(|g| g.bindings.contains(&b))
            .unwrap_or_else(|| panic!("binding {b} not found in any group"))
    }

    fn group_set(groups: &[BindingGroup]) -> Vec<Vec<BindingId>> {
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
