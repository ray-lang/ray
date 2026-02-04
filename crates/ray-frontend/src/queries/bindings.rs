//! Binding-related queries for the incremental query system.
//!
//! This module provides queries for looking up binding information from
//! name resolution results.

use std::collections::HashMap;

use ray_query_macros::query;
use ray_shared::{local_binding::LocalBindingId, node_id::NodeId, resolution::Resolution};

use crate::query::{Database, Query};

use super::{
    deps::{BindingGroupId, binding_group_members},
    resolve::name_resolutions,
};

/// Returns the LocalBindingId for a node if it resolves to a local binding.
///
/// This query looks up name resolution results for an AST node. Nodes that
/// resolve to local bindings (parameters, let-bindings, etc.) will return
/// their LocalBindingId.
///
/// # Arguments
///
/// * `db` - The query database
/// * `node_id` - The AST node identifier
///
/// # Returns
///
/// The LocalBindingId if this node resolves to a local binding, or `None` otherwise.
#[query]
pub fn local_binding_for_node(db: &Database, node_id: NodeId) -> Option<LocalBindingId> {
    let file_id = node_id.owner.file;
    let resolutions = name_resolutions(db, file_id);
    match resolutions.get(&node_id) {
        Some(Resolution::Local(local_id)) => Some(*local_id),
        _ => None,
    }
}

/// Returns all NodeId → LocalBindingId mappings for nodes in a binding group.
///
/// This query aggregates name resolution results for all definitions in a binding
/// group, filtering to only local binding resolutions. This is used by the type
/// checker's copy step to populate `node_tys` from `local_tys`.
///
/// # Arguments
///
/// * `db` - The query database
/// * `group_id` - The binding group identifier
///
/// # Returns
///
/// A map from NodeId to LocalBindingId for all nodes in the group that resolve
/// to local bindings.
#[query]
pub fn local_bindings_for_group(
    db: &Database,
    group_id: BindingGroupId,
) -> HashMap<NodeId, LocalBindingId> {
    let members = binding_group_members(db, group_id);

    // Collect unique files from the group members
    let files: std::collections::HashSet<_> = members.iter().map(|def_id| def_id.file).collect();

    // Aggregate local binding resolutions from all files
    let mut result = HashMap::new();
    for file_id in files {
        let resolutions = name_resolutions(db, file_id);
        for (node_id, resolution) in resolutions.iter() {
            // Only include nodes owned by a def in this group
            if members.contains(&node_id.owner) {
                if let Resolution::Local(local_id) = resolution {
                    result.insert(*node_id, *local_id);
                }
            }
        }
    }

    result
}
