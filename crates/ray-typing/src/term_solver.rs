// Term solver: handles equality constraints and unification.
//
// This implements a simple worklist-based solver as sketched in the spec
// (Section 5.1): it collects all equality constraints in the constraint tree,
// feeds them to the unifier, and applies the evolving substitution back to
// the tree.

use crate::TypeError;
use crate::constraint_tree::ConstraintNode;
use crate::constraints::{Constraint, ConstraintKind};
use crate::types::{Subst, Substitutable};
use crate::unify::unify;

/// Result of the term solver phase over a binding group's constraint tree.
pub struct TermSolveResult {
    /// Any type errors discovered during unification.
    pub errors: Vec<TypeError>,
}

impl TermSolveResult {
    pub fn new() -> Self {
        TermSolveResult { errors: Vec::new() }
    }
}

/// Collect all equality constraints from the constraint tree into a worklist.
fn collect_equalities(root: &ConstraintNode) -> Vec<Constraint> {
    let mut worklist = Vec::new();
    root.walk_children(&mut |node| {
        for c in &node.wanteds {
            if let ConstraintKind::Eq(_) = &c.kind {
                worklist.push(c.clone());
            }
        }
    });
    worklist
}

pub fn solve_equalities(worklist: &[Constraint], subst: &mut Subst) -> TermSolveResult {
    let mut result = TermSolveResult::new();

    for constraint in worklist.iter().rev() {
        let (mut lhs, mut rhs) = match &constraint.kind {
            ConstraintKind::Eq(eq) => (eq.lhs.clone(), eq.rhs.clone()),
            _ => continue,
        };

        // Apply the current substitution to the constraint before unifying,
        // so we always work with the most up-to-date view of types.
        lhs.apply_subst(subst);
        rhs.apply_subst(subst);

        match unify(&lhs, &rhs, subst, &constraint.info) {
            Ok(new_subst) => {
                subst.union(new_subst);
            }
            Err(err) => {
                // Rebuild the error so that it carries the constraint's
                // TypeSystemInfo as well as an equality pair for context.
                let mut info = constraint.info.clone();
                info.equality_type_pair(&lhs, &rhs);
                let enriched = TypeError {
                    kind: err.kind,
                    info,
                };
                result.errors.push(enriched);
            }
        }
    }

    result
}

pub fn solve_equalities_for_node(root: &mut ConstraintNode, subst: &mut Subst) -> TermSolveResult {
    // Collect a global worklist of equality constraints for this binding group.
    let worklist = collect_equalities(root);
    let result = solve_equalities(&worklist, subst);

    // After a successful unification step, propagate the updated
    // substitution through the entire constraint tree so that
    // subsequent constraints see simplified types.
    root.apply_subst(subst);

    result
}
