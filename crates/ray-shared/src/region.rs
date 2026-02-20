//! Region types for lifetime safety analysis.
//!
//! Every reference is internally parameterized by a region representing its
//! validity extent. Regions are tracked outside of `Ty` in a parallel structure
//! and used by the region validation pass to detect lifetime violations.

use serde::{Deserialize, Serialize};

use crate::{local_binding::LocalBindingId, node_id::NodeId};

/// Unique identifier for a region within a single analysis context.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RegionId(pub u32);

/// The kind of region, determining its lifetime extent.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RegionKind {
    /// Heap-allocated: lives as long as refcount > 0.
    /// Produced by `new(T)`, `box(expr)`, `upgrade(x)`.
    Heap,

    /// Stack-scoped: lives as long as the variable's stack frame.
    /// Produced by `&x` or `&mut x` on a stack lvalue.
    Stack(LocalBindingId),

    /// Call-scoped: lives only for the duration of a function call.
    /// Produced by implicit reborrowing at call sites.
    Call(NodeId),

    /// Destructor-scoped: lives only for the destructor body.
    /// The `*mut self` in a `Destruct` implementation.
    Destructor,

    /// Region variable for a function parameter whose concrete region is
    /// unknown until call sites are analyzed. Each reference-type parameter
    /// gets a `Param` region; the function body records constraints on it,
    /// and call sites check those constraints against the argument's concrete
    /// region.
    Param(LocalBindingId),
}

impl RegionKind {
    /// Check whether a value with region `self` can outlive a destination
    /// with region `other`.
    ///
    /// - `Heap` outlives everything.
    /// - `Stack`, `Call`, and `Destructor` can only outlive themselves.
    /// - `Param` cannot be resolved statically — constraints on `Param`
    ///   regions are recorded and checked at call sites instead.
    pub fn can_outlive(&self, other: &RegionKind) -> bool {
        match (self, other) {
            // Heap outlives everything.
            (RegionKind::Heap, _) => true,

            // Stack outlives same stack variable only.
            (RegionKind::Stack(a), RegionKind::Stack(b)) => a == b,

            // Call outlives same call only.
            (RegionKind::Call(a), RegionKind::Call(b)) => a == b,

            // Destructor outlives itself only.
            (RegionKind::Destructor, RegionKind::Destructor) => true,

            // Param regions are checked at call sites, not here.
            // Within the callee body, Param constraints are recorded
            // rather than checked. Reaching this case is a logic error
            // in the region pass — Param should never appear in a
            // direct can_outlive check.
            (RegionKind::Param(_), _) | (_, RegionKind::Param(_)) => false,

            // Everything else fails (e.g., Stack -> Heap, Call -> Heap).
            _ => false,
        }
    }
}

/// Why an outlives constraint was generated — used for error message provenance.
#[derive(Clone, Debug)]
pub enum OutlivesCause {
    /// Storing a reference into a struct field.
    StoreInField {
        struct_expr: NodeId,
        field_name: String,
    },
    /// Returning a reference from a function.
    Return { return_expr: NodeId },
    /// Assigning a reference to a variable or location.
    Assignment { assign_expr: NodeId },
}

/// An outlives constraint: the region of `src` must live at least as long
/// as the region of `dest`.
#[derive(Clone, Debug)]
pub struct OutlivesConstraint {
    pub src: RegionId,
    pub dest: RegionId,
    pub cause: OutlivesCause,
}

/// A region with its kind and provenance information for error messages.
#[derive(Clone, Debug)]
pub struct RegionInfo {
    pub kind: RegionKind,
    /// The expression that created this region.
    pub origin_expr: NodeId,
    /// The name of the variable involved, if known (for error messages).
    pub variable_name: Option<String>,
}

#[cfg(test)]
mod tests {
    use crate::{
        def::DefId, file_id::FileId, local_binding::LocalBindingId, node_id::NodeId,
        region::RegionKind,
    };

    fn make_local(file_idx: u32, def_idx: u32, local_idx: u32) -> LocalBindingId {
        LocalBindingId {
            owner: DefId {
                file: FileId(file_idx),
                index: def_idx,
            },
            index: local_idx,
        }
    }

    fn make_node(file_idx: u32, def_idx: u32, node_idx: u32) -> NodeId {
        NodeId {
            owner: DefId {
                file: FileId(file_idx),
                index: def_idx,
            },
            index: node_idx,
        }
    }

    #[test]
    fn heap_outlives_everything() {
        let local = make_local(0, 0, 0);
        let node = make_node(0, 0, 0);

        assert!(RegionKind::Heap.can_outlive(&RegionKind::Heap));
        assert!(RegionKind::Heap.can_outlive(&RegionKind::Stack(local)));
        assert!(RegionKind::Heap.can_outlive(&RegionKind::Call(node)));
        assert!(RegionKind::Heap.can_outlive(&RegionKind::Destructor));
    }

    #[test]
    fn stack_cannot_outlive_heap() {
        let local = make_local(0, 0, 0);
        assert!(!RegionKind::Stack(local).can_outlive(&RegionKind::Heap));
    }

    #[test]
    fn stack_outlives_same_stack() {
        let local = make_local(0, 0, 0);
        assert!(RegionKind::Stack(local).can_outlive(&RegionKind::Stack(local)));
    }

    #[test]
    fn stack_does_not_outlive_different_stack() {
        let local_a = make_local(0, 0, 0);
        let local_b = make_local(0, 0, 1);
        assert!(!RegionKind::Stack(local_a).can_outlive(&RegionKind::Stack(local_b)));
    }

    #[test]
    fn call_cannot_outlive_heap() {
        let node = make_node(0, 0, 0);
        assert!(!RegionKind::Call(node).can_outlive(&RegionKind::Heap));
    }

    #[test]
    fn call_outlives_same_call() {
        let node = make_node(0, 0, 0);
        assert!(RegionKind::Call(node).can_outlive(&RegionKind::Call(node)));
    }

    #[test]
    fn call_does_not_outlive_different_call() {
        let node_a = make_node(0, 0, 0);
        let node_b = make_node(0, 0, 1);
        assert!(!RegionKind::Call(node_a).can_outlive(&RegionKind::Call(node_b)));
    }

    #[test]
    fn destructor_cannot_outlive_heap() {
        assert!(!RegionKind::Destructor.can_outlive(&RegionKind::Heap));
    }

    #[test]
    fn destructor_outlives_itself() {
        assert!(RegionKind::Destructor.can_outlive(&RegionKind::Destructor));
    }

    #[test]
    fn destructor_cannot_outlive_stack() {
        let local = make_local(0, 0, 0);
        assert!(!RegionKind::Destructor.can_outlive(&RegionKind::Stack(local)));
    }

    #[test]
    fn stack_cannot_outlive_call() {
        let local = make_local(0, 0, 0);
        let node = make_node(0, 0, 0);
        assert!(!RegionKind::Stack(local).can_outlive(&RegionKind::Call(node)));
    }

    #[test]
    fn call_cannot_outlive_stack() {
        let local = make_local(0, 0, 0);
        let node = make_node(0, 0, 0);
        assert!(!RegionKind::Call(node).can_outlive(&RegionKind::Stack(local)));
    }

    #[test]
    fn param_cannot_outlive_anything_statically() {
        let local = make_local(0, 0, 0);
        let node = make_node(0, 0, 0);

        assert!(!RegionKind::Param(local).can_outlive(&RegionKind::Heap));
        assert!(!RegionKind::Param(local).can_outlive(&RegionKind::Stack(local)));
        assert!(!RegionKind::Param(local).can_outlive(&RegionKind::Call(node)));
        assert!(!RegionKind::Param(local).can_outlive(&RegionKind::Destructor));
    }

    #[test]
    fn nothing_outlives_param_statically() {
        let local = make_local(0, 0, 0);

        assert!(!RegionKind::Stack(local).can_outlive(&RegionKind::Param(local)));
        assert!(!RegionKind::Destructor.can_outlive(&RegionKind::Param(local)));
        // Heap CAN outlive Param because Heap outlives everything.
        assert!(RegionKind::Heap.can_outlive(&RegionKind::Param(local)));
    }
}
