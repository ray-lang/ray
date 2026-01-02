//! Unification and substitution primitives for the type system.
//!
//! This module defines the basic substitution map and the public `unify` API
//! that the term solver will use to discharge equality constraints.
use std::collections::HashSet;

use ray_shared::ty::{Ty, TyVar};

use crate::{
    TypeError,
    info::TypeSystemInfo,
    types::{Subst, Substitutable, TyScheme},
};

fn occurs_in(var: &TyVar, ty: &Ty, subst: &Subst) -> bool {
    let mut ty = ty.clone();
    ty.apply_subst(subst);
    match ty {
        Ty::Var(ref v) => v == var,
        Ty::Const(_) | Ty::Any | Ty::Never => false,
        Ty::Func(ref params, ref ret) => {
            params.iter().any(|t| occurs_in(var, t, subst)) || occurs_in(var, ret, subst)
        }
        Ty::Ref(ref inner) | Ty::RawPtr(ref inner) => occurs_in(var, inner, subst),
        Ty::Proj(_, ref args) | Ty::Tuple(ref args) => {
            args.iter().any(|t| occurs_in(var, t, subst))
        }
        Ty::Array(ref elem, _) => occurs_in(var, elem, subst),
    }
}

fn bind_var(
    var: TyVar,
    mut ty: Ty,
    subst: &mut Subst,
    info: &TypeSystemInfo,
) -> Result<(), TypeError> {
    ty.apply_subst(subst);

    if let Ty::Var(ref v) = ty {
        if *v == var {
            // Trivial equality.
            return Ok(());
        }
    }

    if var.is_skolem() {
        let err = match &ty {
            Ty::Var(other) if other.is_skolem() => {
                TypeError::skolem_versus_skolem(var, other.clone(), info.clone())
            }
            Ty::Const(_) | Ty::Proj(_, _) => {
                TypeError::skolem_versus_constant(var, ty, info.clone())
            }
            _ => TypeError::escaping_skolem(var, ty, info.clone()),
        };
        return Err(err);
    }

    // Treat non-meta variables as rigid: they can only unify with themselves.
    if !var.is_meta() {
        return Err(TypeError::rigid_var(var, ty, info.clone()));
    }

    if occurs_in(&var, &ty, subst) {
        return Err(TypeError::occurs_check(var, ty, info.clone()));
    }

    subst.insert(var, ty);
    Ok(())
}

/// Unify two types, updating the substitution map in place.
///
/// The intended semantics follow the equality-constraint behavior described in
/// the type-system spec: primitive and nominal constructors must match, meta
/// variables may be assigned (respecting occurs checks), and rigid variables
/// may not be unified with incompatible types.
pub fn unify(
    lhs: &Ty,
    rhs: &Ty,
    global_subst: &Subst,
    info: &TypeSystemInfo,
) -> Result<Subst, TypeError> {
    // Create a fresh, local substitution
    let mut subst = global_subst.clone();

    // Apply the global substitution to the types
    let mut lhs = lhs.clone();
    lhs.apply_subst(&global_subst);
    let mut rhs = rhs.clone();
    rhs.apply_subst(&global_subst);

    match (lhs, rhs) {
        // Bottom type `never` unifies with anything without constraining it.
        (Ty::Never, _) | (_, Ty::Never) => { /* ignore */ }

        // Top-like type `any` unifies with anything, without adding constraints.
        (Ty::Any, _) | (_, Ty::Any) => { /* ignore */ }

        (Ty::Const(p1), Ty::Const(p2)) => {
            if p1 != p2 {
                return Err(TypeError::mismatch(
                    Ty::Const(p1),
                    Ty::Const(p2),
                    info.clone(),
                ));
            }
        }

        (Ty::Var(v1), Ty::Var(v2)) => {
            if v1 == v2 {
                /* ignore */
            } else if v1.is_skolem() && v2.is_skolem() {
                return Err(TypeError::skolem_versus_skolem(v1, v2, info.clone()));
            } else if v1.is_meta() && !v2.is_meta() {
                // Prefer binding metas to rigid vars.
                bind_var(v1, Ty::Var(v2), &mut subst, info)?;
            } else if v2.is_meta() && !v1.is_meta() {
                // Prefer binding metas to rigid vars.
                bind_var(v2, Ty::Var(v1), &mut subst, info)?;
            } else if v1.is_meta() && v2.is_meta() {
                bind_var(v1, Ty::Var(v2), &mut subst, info)?;
            } else if v1.is_skolem() || v2.is_skolem() {
                // A skolem cannot unify with a distinct rigid variable.
                let (skolem, other) = if v1.is_skolem() { (v1, v2) } else { (v2, v1) };
                return Err(TypeError::skolem_versus_constant(
                    skolem,
                    Ty::Var(other),
                    info.clone(),
                ));
            } else {
                // Distinct schema vars are rigid.
                return Err(TypeError::rigid_var(v1, Ty::Var(v2), info.clone()));
            }
        }

        (Ty::Var(v), ty) | (ty, Ty::Var(v)) => {
            bind_var(v, ty, &mut subst, info)?;
        }

        (Ty::Func(ps1, r1), Ty::Func(ps2, r2)) => {
            if ps1.len() != ps2.len() {
                // We currently treat arity mismatches as a generic mismatch.
                return Err(TypeError::mismatch(
                    Ty::Func(ps1, r1),
                    Ty::Func(ps2, r2),
                    info.clone(),
                ));
            }
            for (a, b) in ps1.iter().zip(ps2.iter()) {
                subst = unify(a, b, &subst, info)?;
            }
            subst = unify(&r1, &r2, &subst, info)?;
        }

        (Ty::Ref(t1), Ty::Ref(t2)) => {
            subst = unify(&t1, &t2, &subst, info)?;
        }
        (Ty::RawPtr(t1), Ty::RawPtr(t2)) => {
            subst = unify(&t1, &t2, &subst, info)?;
        }

        (Ty::Proj(p1, args1), Ty::Proj(p2, args2)) => {
            if p1 != p2 || args1.len() != args2.len() {
                return Err(TypeError::mismatch(
                    Ty::Proj(p1, args1),
                    Ty::Proj(p2, args2),
                    info.clone(),
                ));
            }
            for (a, b) in args1.iter().zip(args2.iter()) {
                subst = unify(a, b, &subst, info)?;
            }
        }

        (Ty::Tuple(elems1), Ty::Tuple(elems2)) => {
            if elems1.len() != elems2.len() {
                return Err(TypeError::mismatch(
                    Ty::Tuple(elems1),
                    Ty::Tuple(elems2),
                    info.clone(),
                ));
            }
            for (a, b) in elems1.iter().zip(elems2.iter()) {
                subst = unify(a, b, &subst, info)?;
            }
        }

        (Ty::Array(e1, n1), Ty::Array(e2, n2)) => {
            if n1 != n2 {
                return Err(TypeError::mismatch(
                    Ty::Array(e1, n1),
                    Ty::Array(e2, n2),
                    info.clone(),
                ));
            }
            subst = unify(&e1, &e2, &subst, info)?;
        }

        // All other constructor mismatches are errors.
        (t1, t2) => return Err(TypeError::mismatch(t1, t2, info.clone())),
    }

    Ok(subst)
}

#[cfg(test)]
mod tests {
    use ray_shared::ty::{Ty, TyVar};

    use crate::info::TypeSystemInfo;
    use crate::types::Subst;

    use super::unify;

    #[test]
    fn unify_binds_meta_to_schema_var() {
        let info = TypeSystemInfo::default();
        let subst = Subst::new();

        let s0 = TyVar::new("?s0");
        let t0 = TyVar::new("?t0");

        let out = unify(&Ty::Var(s0.clone()), &Ty::Var(t0.clone()), &subst, &info).unwrap();
        assert_eq!(out.get(&t0), Some(&Ty::Var(s0.clone())));

        let out2 = unify(&Ty::Var(t0.clone()), &Ty::Var(s0.clone()), &subst, &info).unwrap();
        assert_eq!(out2.get(&t0), Some(&Ty::Var(s0)));
    }
}

/// Convenience wrapper that computes the most-general unifier of two monotypes.
///
/// This mirrors the legacy `ray_typing::top::mgu` helper so existing callers
/// in `ray-core` can continue to request an mgu while we migrate the rest of
/// the solver stack. The returned pair matches the old signature: the first
/// element is the (already-simplified) left-hand type, and the second is the
/// resulting substitution.
pub fn mgu(lhs: &Ty, rhs: &Ty) -> Result<(bool, Subst), TypeError> {
    let info = TypeSystemInfo::new();
    let subst = Subst::new();
    unify(lhs, rhs, &subst, &info).map(|s| (true, s))
}

pub fn match_scheme_vars(poly_ty: &TyScheme, callee_ty: &TyScheme) -> Option<Subst> {
    let poly_vars: HashSet<TyVar> = poly_ty.vars.iter().cloned().collect();
    let mut subst = Subst::new();
    if match_ty(poly_ty.mono(), callee_ty.mono(), &poly_vars, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

pub fn match_ty(poly: &Ty, callee: &Ty, poly_vars: &HashSet<TyVar>, subst: &mut Subst) -> bool {
    let mut poly_norm = poly.clone();
    poly_norm.apply_subst(subst);

    match &poly_norm {
        Ty::Var(v) if poly_vars.contains(v) => {
            if let Ty::Var(callee_v) = callee {
                if callee_v == v {
                    return true;
                }
            }
            subst.insert(v.clone(), callee.clone());
            true
        }
        _ => match (&poly_norm, callee) {
            (Ty::Const(a), Ty::Const(b)) => a == b,
            (Ty::Var(a), Ty::Var(b)) => a == b,
            (Ty::Func(a_params, a_ret), Ty::Func(b_params, b_ret)) => {
                a_params.len() == b_params.len()
                    && a_params
                        .iter()
                        .zip(b_params.iter())
                        .all(|(a, b)| match_ty(a, b, poly_vars, subst))
                    && match_ty(a_ret, b_ret, poly_vars, subst)
            }
            (Ty::Ref(a), Ty::Ref(b)) | (Ty::RawPtr(a), Ty::RawPtr(b)) => {
                match_ty(a, b, poly_vars, subst)
            }
            (Ty::Proj(a_name, a_args), Ty::Proj(b_name, b_args)) => {
                a_name == b_name
                    && a_args.len() == b_args.len()
                    && a_args
                        .iter()
                        .zip(b_args.iter())
                        .all(|(a, b)| match_ty(a, b, poly_vars, subst))
            }
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|(a, b)| match_ty(a, b, poly_vars, subst))
            }
            (Ty::Array(a_elem, a_len), Ty::Array(b_elem, b_len)) => {
                a_len == b_len && match_ty(a_elem, b_elem, poly_vars, subst)
            }
            (Ty::Any, Ty::Any) | (Ty::Never, Ty::Never) => true,
            _ => false,
        },
    }
}
