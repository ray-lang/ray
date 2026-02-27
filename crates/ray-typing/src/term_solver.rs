// Term solver: handles equality and subtype constraints via unification.
//
// This implements a simple worklist-based solver as sketched in the spec
// (Section 5.1): it collects all term-level constraints in the constraint tree,
// feeds them to the unifier, and applies the evolving substitution back to
// the tree.

use ray_shared::ty::Ty;

use crate::{
    TypeError,
    constraints::{Constraint, ConstraintKind},
    types::{Subst, Substitutable},
    unify::unify,
};

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

/// Solve all equality constraints (`Eq`) in the worklist.
///
/// Called pre-children so that type annotations and known equalities are
/// committed to `subst` before child nodes are solved.
pub fn solve_equalities(worklist: &[Constraint], subst: &mut Subst) -> TermSolveResult {
    let mut result = TermSolveResult::new();

    for constraint in worklist.iter().rev() {
        let ConstraintKind::Eq(eq) = &constraint.kind else {
            continue;
        };

        let mut lhs = eq.lhs.clone();
        let mut rhs = eq.rhs.clone();

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
                result.errors.push(TypeError {
                    kind: err.kind,
                    info,
                });
            }
        }
    }

    result
}

/// Commit subtype constraints by unifying sub and super types.
///
/// Called post-children so that bindings established during child solving are
/// visible when unifying sub and super types.
///
/// - `never <: T` always holds (no unification needed).
/// - `T <: any` always holds (no unification needed).
/// - Otherwise: unify `sub` and `sup` and commit bindings to `subst`.
pub fn solve_subtypes(worklist: &[Constraint], subst: &mut Subst) -> TermSolveResult {
    let mut result = TermSolveResult::new();

    for constraint in worklist.iter().rev() {
        let ConstraintKind::Subtype(st) = &constraint.kind else {
            continue;
        };

        let mut lhs = st.sub.clone();
        let mut rhs = st.sup.clone();

        // Apply the current substitution before unifying,
        // so we always work with the most up-to-date view of types.
        lhs.apply_subst(subst);
        rhs.apply_subst(subst);

        // `never <: T` always holds.
        if matches!(lhs, Ty::Never) {
            continue;
        }
        // `T <: any` always holds.
        if matches!(rhs, Ty::Any) {
            continue;
        }

        match unify(&lhs, &rhs, subst, &constraint.info) {
            Ok(new_subst) => {
                subst.union(new_subst);
            }
            Err(err) => {
                let mut info = constraint.info.clone();
                info.equality_type_pair(&lhs, &rhs);
                result.errors.push(TypeError {
                    kind: err.kind,
                    info,
                });
            }
        }
    }

    result
}
