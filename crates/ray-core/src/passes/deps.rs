use std::collections::HashMap;

use ray_shared::{
    def::DefId,
    node_id::NodeId,
    resolution::{DefTarget, Resolution},
};
use ray_typing::binding_groups::BindingGraph;

/// Extract the definition dependencies for a single definition.
///
/// Returns the list of workspace DefIds that this definition references.
/// This is used to build the dependency graph for incremental compilation.
pub fn def_deps(def_id: DefId, resolutions: &HashMap<NodeId, Resolution>) -> Vec<DefId> {
    resolutions
        .iter()
        .filter(|(node_id, _)| node_id.owner == def_id)
        .filter_map(|(_, res)| match res {
            Resolution::Def(DefTarget::Workspace(target)) => Some(*target),
            _ => None,
        })
        .collect()
}

/// Build a dependency graph over DefIds from the resolution table.
///
/// This produces a `BindingGraph<DefId>` that can be used to compute
/// binding groups (SCCs) for typechecking.
pub fn build_binding_graph(
    defs: &[DefId],
    resolutions: &HashMap<NodeId, Resolution>,
) -> BindingGraph<DefId> {
    let mut graph = BindingGraph::new();

    for &def_id in defs {
        graph.add_binding(def_id);
        for dep in def_deps(def_id, resolutions) {
            graph.add_edge(def_id, dep);
        }
    }

    graph
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::DefId,
        file_id::FileId,
        local_binding::LocalBindingId,
        node_id::NodeId,
        pathlib::{ItemPath, ModulePath},
        resolution::{DefTarget, Resolution},
    };
    use ray_typing::binding_groups::{BindingId, LegacyBindingGraph};

    use crate::passes::deps::{build_binding_graph, def_deps};

    #[test]
    fn def_deps_extracts_workspace_targets() {
        let file = FileId(0);
        let def_a = DefId::new(file, 1);
        let def_b = DefId::new(file, 2);
        let def_c = DefId::new(file, 3);

        // Create nodes owned by def_a that reference def_b and def_c
        let node1 = NodeId {
            owner: def_a,
            index: 1,
        };
        let node2 = NodeId {
            owner: def_a,
            index: 2,
        };
        let node3 = NodeId {
            owner: def_a,
            index: 3,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node1, Resolution::Def(DefTarget::Workspace(def_b)));
        resolutions.insert(node2, Resolution::Def(DefTarget::Workspace(def_c)));
        // Local binding should be ignored
        resolutions.insert(node3, Resolution::Local(LocalBindingId::new(def_a, 0)));

        let deps = def_deps(def_a, &resolutions);
        assert_eq!(deps.len(), 2);
        assert!(deps.contains(&def_b));
        assert!(deps.contains(&def_c));
    }

    #[test]
    fn def_deps_ignores_other_owners() {
        let file = FileId(0);
        let def_a = DefId::new(file, 1);
        let def_b = DefId::new(file, 2);
        let def_c = DefId::new(file, 3);

        // Node owned by def_b, not def_a
        let node_from_b = NodeId {
            owner: def_b,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node_from_b, Resolution::Def(DefTarget::Workspace(def_c)));

        // Should return empty since no nodes are owned by def_a
        let deps = def_deps(def_a, &resolutions);
        assert!(deps.is_empty());
    }

    #[test]
    fn def_deps_ignores_library_targets() {
        let file = FileId(0);
        let def_a = DefId::new(file, 1);

        let node1 = NodeId {
            owner: def_a,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(
            node1,
            Resolution::Def(DefTarget::Library(ItemPath {
                module: ModulePath::from("io"),
                item: vec!["print".to_string()],
            })),
        );

        // Library targets should be ignored
        let deps = def_deps(def_a, &resolutions);
        assert!(deps.is_empty());
    }

    #[test]
    fn def_deps_empty_resolutions() {
        let def_a = DefId::new(FileId(0), 1);
        let resolutions = HashMap::new();

        let deps = def_deps(def_a, &resolutions);
        assert!(deps.is_empty());
    }

    // Tests for build_binding_graph

    #[test]
    fn build_binding_graph_creates_edges() {
        let file = FileId(0);
        let def_a = DefId::new(file, 1);
        let def_b = DefId::new(file, 2);
        let def_c = DefId::new(file, 3);

        // def_a references def_b, def_b references def_c
        let node_a1 = NodeId {
            owner: def_a,
            index: 1,
        };
        let node_b1 = NodeId {
            owner: def_b,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node_a1, Resolution::Def(DefTarget::Workspace(def_b)));
        resolutions.insert(node_b1, Resolution::Def(DefTarget::Workspace(def_c)));

        let graph = build_binding_graph(&[def_a, def_b, def_c], &resolutions);

        // Check edges exist
        assert!(graph.edges.get(&def_a).unwrap().contains(&def_b));
        assert!(graph.edges.get(&def_b).unwrap().contains(&def_c));
        assert!(graph.edges.get(&def_c).unwrap().is_empty());
    }

    #[test]
    fn build_binding_graph_mutual_recursion() {
        let file = FileId(0);
        let def_a = DefId::new(file, 1);
        let def_b = DefId::new(file, 2);

        // def_a references def_b, def_b references def_a (mutual recursion)
        let node_a1 = NodeId {
            owner: def_a,
            index: 1,
        };
        let node_b1 = NodeId {
            owner: def_b,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node_a1, Resolution::Def(DefTarget::Workspace(def_b)));
        resolutions.insert(node_b1, Resolution::Def(DefTarget::Workspace(def_a)));

        let graph = build_binding_graph(&[def_a, def_b], &resolutions);

        // Both should be in same SCC
        let groups = graph.compute_binding_groups();
        assert_eq!(groups.len(), 1);
        assert!(groups[0].bindings.contains(&def_a));
        assert!(groups[0].bindings.contains(&def_b));
    }

    #[test]
    fn build_binding_graph_computes_sccs() {
        let file = FileId(0);
        let def_a = DefId::new(file, 1);
        let def_b = DefId::new(file, 2);
        let def_c = DefId::new(file, 3);

        // def_a -> def_b -> def_c (linear chain, 3 separate SCCs)
        let node_a1 = NodeId {
            owner: def_a,
            index: 1,
        };
        let node_b1 = NodeId {
            owner: def_b,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node_a1, Resolution::Def(DefTarget::Workspace(def_b)));
        resolutions.insert(node_b1, Resolution::Def(DefTarget::Workspace(def_c)));

        let graph = build_binding_graph(&[def_a, def_b, def_c], &resolutions);
        let groups = graph.compute_binding_groups();

        // Should have 3 groups, in order: def_c, def_b, def_a
        assert_eq!(groups.len(), 3);

        // Find indices
        let idx_a = groups
            .iter()
            .position(|g| g.bindings.contains(&def_a))
            .unwrap();
        let idx_b = groups
            .iter()
            .position(|g| g.bindings.contains(&def_b))
            .unwrap();
        let idx_c = groups
            .iter()
            .position(|g| g.bindings.contains(&def_c))
            .unwrap();

        // Dependencies should come before dependents
        assert!(idx_c < idx_b, "def_c should come before def_b");
        assert!(idx_b < idx_a, "def_b should come before def_a");
    }

    // SCC equivalence tests (Phase 0.E Step 3)
    //
    // These tests verify that the new `build_binding_graph` + Tarjan's SCC
    // produces equivalent binding groups to what the legacy binding pass would
    // produce, modulo ID representation (DefId vs BindingId).
    //
    // The key invariant: given the same dependency structure, both systems
    // should compute:
    // 1. The same number of binding groups
    // 2. The same grouping (which bindings are mutually recursive)
    // 3. The same topological order (dependencies before dependents)

    /// Helper to build a legacy binding graph with the same structure as
    /// a DefId-based graph, for comparison purposes.
    fn build_legacy_graph_with_structure(
        edges: &[(u64, u64)],
        bindings: &[u64],
    ) -> LegacyBindingGraph {
        let mut graph = LegacyBindingGraph::new();
        for &b in bindings {
            graph.add_binding(BindingId(b));
        }
        for &(from, to) in edges {
            graph.add_edge(BindingId(from), BindingId(to));
        }
        graph
    }

    #[test]
    fn scc_equivalence_linear_chain() {
        // Linear chain: a -> b -> c (no cycles)
        // Legacy: BindingId(0) -> BindingId(1) -> BindingId(2)
        // New: DefId(file, 0) -> DefId(file, 1) -> DefId(file, 2)
        //
        // Both should produce 3 separate SCCs in order: c, b, a

        // Legacy approach
        let legacy_graph = build_legacy_graph_with_structure(&[(0, 1), (1, 2)], &[0, 1, 2]);
        let legacy_groups = legacy_graph.compute_binding_groups();

        // New approach
        let file = FileId(0);
        let def_a = DefId::new(file, 0);
        let def_b = DefId::new(file, 1);
        let def_c = DefId::new(file, 2);

        let node_a = NodeId {
            owner: def_a,
            index: 1,
        };
        let node_b = NodeId {
            owner: def_b,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node_a, Resolution::Def(DefTarget::Workspace(def_b)));
        resolutions.insert(node_b, Resolution::Def(DefTarget::Workspace(def_c)));

        let new_graph = build_binding_graph(&[def_a, def_b, def_c], &resolutions);
        let new_groups = new_graph.compute_binding_groups();

        // Both should have 3 groups
        assert_eq!(
            legacy_groups.len(),
            new_groups.len(),
            "group count mismatch"
        );
        assert_eq!(legacy_groups.len(), 3);

        // Each group should have exactly 1 binding
        for (i, (lg, ng)) in legacy_groups.iter().zip(new_groups.iter()).enumerate() {
            assert_eq!(
                lg.bindings.len(),
                ng.bindings.len(),
                "group {} size mismatch",
                i
            );
            assert_eq!(lg.bindings.len(), 1);
        }

        // Verify topological order: dependencies come before dependents
        let legacy_idx_a = legacy_groups
            .iter()
            .position(|g| g.bindings.contains(&BindingId(0)))
            .unwrap();
        let legacy_idx_b = legacy_groups
            .iter()
            .position(|g| g.bindings.contains(&BindingId(1)))
            .unwrap();
        let legacy_idx_c = legacy_groups
            .iter()
            .position(|g| g.bindings.contains(&BindingId(2)))
            .unwrap();

        let new_idx_a = new_groups
            .iter()
            .position(|g| g.bindings.contains(&def_a))
            .unwrap();
        let new_idx_b = new_groups
            .iter()
            .position(|g| g.bindings.contains(&def_b))
            .unwrap();
        let new_idx_c = new_groups
            .iter()
            .position(|g| g.bindings.contains(&def_c))
            .unwrap();

        // Both should have c before b before a
        assert!(legacy_idx_c < legacy_idx_b && legacy_idx_b < legacy_idx_a);
        assert!(new_idx_c < new_idx_b && new_idx_b < new_idx_a);
    }

    #[test]
    fn scc_equivalence_mutual_recursion() {
        // Mutual recursion: a <-> b, c depends on a
        // Legacy: BindingId(0) <-> BindingId(1), BindingId(2) -> BindingId(0)
        // New: DefId(file, 0) <-> DefId(file, 1), DefId(file, 2) -> DefId(file, 0)
        //
        // Both should produce 2 SCCs: {a, b} and {c}, with {a, b} before {c}

        // Legacy approach
        let legacy_graph = build_legacy_graph_with_structure(&[(0, 1), (1, 0), (2, 0)], &[0, 1, 2]);
        let legacy_groups = legacy_graph.compute_binding_groups();

        // New approach
        let file = FileId(0);
        let def_a = DefId::new(file, 0);
        let def_b = DefId::new(file, 1);
        let def_c = DefId::new(file, 2);

        let node_a1 = NodeId {
            owner: def_a,
            index: 1,
        };
        let node_b1 = NodeId {
            owner: def_b,
            index: 1,
        };
        let node_c1 = NodeId {
            owner: def_c,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node_a1, Resolution::Def(DefTarget::Workspace(def_b)));
        resolutions.insert(node_b1, Resolution::Def(DefTarget::Workspace(def_a)));
        resolutions.insert(node_c1, Resolution::Def(DefTarget::Workspace(def_a)));

        let new_graph = build_binding_graph(&[def_a, def_b, def_c], &resolutions);
        let new_groups = new_graph.compute_binding_groups();

        // Both should have 2 groups
        assert_eq!(
            legacy_groups.len(),
            new_groups.len(),
            "group count mismatch"
        );
        assert_eq!(legacy_groups.len(), 2);

        // Find the mutually recursive group (size 2) and the singleton (size 1)
        let legacy_mutual = legacy_groups
            .iter()
            .find(|g| g.bindings.len() == 2)
            .unwrap();
        let legacy_singleton = legacy_groups
            .iter()
            .find(|g| g.bindings.len() == 1)
            .unwrap();

        let new_mutual = new_groups.iter().find(|g| g.bindings.len() == 2).unwrap();
        let new_singleton = new_groups.iter().find(|g| g.bindings.len() == 1).unwrap();

        // The mutual group should contain the mutually recursive bindings
        assert!(legacy_mutual.bindings.contains(&BindingId(0)));
        assert!(legacy_mutual.bindings.contains(&BindingId(1)));

        assert!(new_mutual.bindings.contains(&def_a));
        assert!(new_mutual.bindings.contains(&def_b));

        // The singleton should be the one that depends on the mutual group
        assert!(legacy_singleton.bindings.contains(&BindingId(2)));
        assert!(new_singleton.bindings.contains(&def_c));

        // The mutual group should come before the singleton (dependencies first)
        let legacy_mutual_idx = legacy_groups
            .iter()
            .position(|g| g.bindings.len() == 2)
            .unwrap();
        let legacy_singleton_idx = legacy_groups
            .iter()
            .position(|g| g.bindings.len() == 1)
            .unwrap();
        assert!(legacy_mutual_idx < legacy_singleton_idx);

        let new_mutual_idx = new_groups
            .iter()
            .position(|g| g.bindings.len() == 2)
            .unwrap();
        let new_singleton_idx = new_groups
            .iter()
            .position(|g| g.bindings.len() == 1)
            .unwrap();
        assert!(new_mutual_idx < new_singleton_idx);
    }

    #[test]
    fn scc_equivalence_complex_cycle() {
        // Complex: a -> b -> c -> a (3-way cycle), d -> b (depends on cycle)
        // All of a, b, c should be in one SCC, d in another
        // SCC {a, b, c} should come before {d}

        // Legacy approach
        let legacy_graph =
            build_legacy_graph_with_structure(&[(0, 1), (1, 2), (2, 0), (3, 1)], &[0, 1, 2, 3]);
        let legacy_groups = legacy_graph.compute_binding_groups();

        // New approach
        let file = FileId(0);
        let def_a = DefId::new(file, 0);
        let def_b = DefId::new(file, 1);
        let def_c = DefId::new(file, 2);
        let def_d = DefId::new(file, 3);

        let node_a = NodeId {
            owner: def_a,
            index: 1,
        };
        let node_b = NodeId {
            owner: def_b,
            index: 1,
        };
        let node_c = NodeId {
            owner: def_c,
            index: 1,
        };
        let node_d = NodeId {
            owner: def_d,
            index: 1,
        };

        let mut resolutions = HashMap::new();
        resolutions.insert(node_a, Resolution::Def(DefTarget::Workspace(def_b)));
        resolutions.insert(node_b, Resolution::Def(DefTarget::Workspace(def_c)));
        resolutions.insert(node_c, Resolution::Def(DefTarget::Workspace(def_a)));
        resolutions.insert(node_d, Resolution::Def(DefTarget::Workspace(def_b)));

        let new_graph = build_binding_graph(&[def_a, def_b, def_c, def_d], &resolutions);
        let new_groups = new_graph.compute_binding_groups();

        // Both should have 2 groups
        assert_eq!(
            legacy_groups.len(),
            new_groups.len(),
            "group count mismatch"
        );
        assert_eq!(legacy_groups.len(), 2);

        // Find the cycle group (size 3) and the singleton (size 1)
        let legacy_cycle = legacy_groups
            .iter()
            .find(|g| g.bindings.len() == 3)
            .unwrap();
        let legacy_singleton = legacy_groups
            .iter()
            .find(|g| g.bindings.len() == 1)
            .unwrap();

        let new_cycle = new_groups.iter().find(|g| g.bindings.len() == 3).unwrap();
        let new_singleton = new_groups.iter().find(|g| g.bindings.len() == 1).unwrap();

        // The cycle group should contain a, b, c
        assert!(legacy_cycle.bindings.contains(&BindingId(0)));
        assert!(legacy_cycle.bindings.contains(&BindingId(1)));
        assert!(legacy_cycle.bindings.contains(&BindingId(2)));

        assert!(new_cycle.bindings.contains(&def_a));
        assert!(new_cycle.bindings.contains(&def_b));
        assert!(new_cycle.bindings.contains(&def_c));

        // The singleton should be d
        assert!(legacy_singleton.bindings.contains(&BindingId(3)));
        assert!(new_singleton.bindings.contains(&def_d));

        // The cycle group should come before the singleton
        let legacy_cycle_idx = legacy_groups
            .iter()
            .position(|g| g.bindings.len() == 3)
            .unwrap();
        let legacy_singleton_idx = legacy_groups
            .iter()
            .position(|g| g.bindings.len() == 1)
            .unwrap();
        assert!(legacy_cycle_idx < legacy_singleton_idx);

        let new_cycle_idx = new_groups
            .iter()
            .position(|g| g.bindings.len() == 3)
            .unwrap();
        let new_singleton_idx = new_groups
            .iter()
            .position(|g| g.bindings.len() == 1)
            .unwrap();
        assert!(new_cycle_idx < new_singleton_idx);
    }

    #[test]
    fn scc_equivalence_isolated_bindings() {
        // Isolated bindings with no dependencies
        // Each should be its own SCC

        // Legacy approach
        let legacy_graph = build_legacy_graph_with_structure(&[], &[0, 1, 2]);
        let legacy_groups = legacy_graph.compute_binding_groups();

        // New approach
        let file = FileId(0);
        let def_a = DefId::new(file, 0);
        let def_b = DefId::new(file, 1);
        let def_c = DefId::new(file, 2);

        let resolutions = HashMap::new(); // No resolutions = no dependencies

        let new_graph = build_binding_graph(&[def_a, def_b, def_c], &resolutions);
        let new_groups = new_graph.compute_binding_groups();

        // Both should have 3 groups (one per binding)
        assert_eq!(
            legacy_groups.len(),
            new_groups.len(),
            "group count mismatch"
        );
        assert_eq!(legacy_groups.len(), 3);

        // Each group should have exactly 1 binding
        for g in &legacy_groups {
            assert_eq!(g.bindings.len(), 1);
        }
        for g in &new_groups {
            assert_eq!(g.bindings.len(), 1);
        }
    }
}
