//! Binding-related queries for the incremental query system.
//!
//! This module provides queries for looking up binding information from
//! pattern records created during type checking.

use ray_query_macros::query;
use ray_shared::{local_binding::LocalBindingId, node_id::NodeId};
use ray_typing::PatternKind;

use crate::{
    queries::deps::binding_group_for_def,
    query::{Database, Query},
};

use super::typecheck::typecheck_group_input;

/// Returns the LocalBindingId for a pattern node if it introduces a binding.
///
/// This query looks up pattern metadata for an AST node during type checking.
/// Only pattern nodes that introduce bindings (via `PatternKind::Binding` or
/// `PatternKind::Deref`) will return a LocalBindingId.
///
/// # Arguments
///
/// * `db` - The query database
/// * `node_id` - The pattern node identifier
///
/// # Returns
///
/// The LocalBindingId if this pattern introduces a binding, or `None` otherwise.
#[query]
pub fn local_binding_for_node(db: &Database, node_id: NodeId) -> Option<LocalBindingId> {
    let def_id = node_id.owner;
    let group_id = binding_group_for_def(db, def_id);
    let input = typecheck_group_input(db, group_id);
    let record = input.pattern_records.get(&node_id)?;
    match &record.kind {
        PatternKind::Binding { binding } => Some(*binding),
        PatternKind::Deref { binding } => Some(*binding),
        _ => None,
    }
}
