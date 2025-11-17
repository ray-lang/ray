use std::fmt::Display;

use crate::TyVar;

use super::{OrderedTypeSynonyms, Subst, Ty};

#[derive(Debug, PartialEq, Eq)]
pub enum UnificationError<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    TypeMismatch(T, T),
    ConstantMismatch(String, String),
    InfiniteType(V),
}

impl<T, V> Display for UnificationError<T, V>
where
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            UnificationError::TypeMismatch(lhs, rhs) => {
                write!(f, "type mismatch: {} != {}", lhs, rhs)
            }
            UnificationError::ConstantMismatch(lhs, rhs) => {
                write!(f, "constant mismatch: {} != {}", lhs, rhs)
            }
            UnificationError::InfiniteType(id) => write!(f, "infinite type {}", id),
        }
    }
}

pub fn mgu<T, V>(lhs: &T, rhs: &T) -> Result<(bool, Subst<V, T>), UnificationError<T, V>>
where
    T: Ty<V>,
    V: TyVar,
{
    let subst = Subst::new();
    let synonyms = OrderedTypeSynonyms::new();
    mgu_with_synonyms(lhs, rhs, &subst, &synonyms)
}

pub fn mgu_with_synonyms<T, V>(
    lhs: &T,
    rhs: &T,
    subst: &Subst<V, T>,
    synonyms: &OrderedTypeSynonyms<T, V>,
) -> Result<(bool, Subst<V, T>), UnificationError<T, V>>
where
    T: Ty<V>,
    V: TyVar,
{
    let (lhs_lsp, lhs_tys) = lhs.left_spine();
    let (rhs_lsp, rhs_tys) = rhs.left_spine();

    log::debug!(
        "[mgu_with_synonyms] lhs_lsp={:?}, lhs_tys={:?}, rhs_lsp={:?}, rhs_tys={:?}",
        lhs_lsp,
        lhs_tys,
        rhs_lsp,
        rhs_tys
    );

    match (lhs_lsp.maybe_var(), rhs_lsp.maybe_var()) {
        (Some(tyvar), _) if lhs_tys.is_empty() => return mgu_type_var(tyvar, rhs, subst, synonyms),
        (_, Some(tyvar)) if rhs_tys.is_empty() => return mgu_type_var(tyvar, lhs, subst, synonyms),
        _ => {}
    }

    match (lhs_lsp.maybe_const(), rhs_lsp.maybe_const()) {
        (Some(a), Some(b)) if a == b && !synonyms.is_phantom_synonym(a) => {
            return mgu_slices(&lhs_tys, &rhs_tys, subst, synonyms);
        }
        (Some(a), Some(b)) => {
            return match synonyms.expand_ordered(lhs.clone(), rhs.clone()) {
                Some((a, b)) => match mgu_with_synonyms(&a, &b, subst, synonyms) {
                    Ok((_, subst)) => Ok((true, subst)),
                    Err(e) => Err(e),
                },
                _ => Err(UnificationError::ConstantMismatch(
                    a.to_string(),
                    b.to_string(),
                )),
            };
        }
        _ => {}
    }

    match (lhs.maybe_app(), rhs.maybe_app()) {
        (Some((l1, r1)), Some((l2, r2))) => {
            let mut lhs = vec![l1];
            lhs.extend(r1.into_iter());
            let mut rhs = vec![l2];
            rhs.extend(r2.into_iter());
            return mgu_slices(&lhs[..], &rhs[..], subst, synonyms);
        }
        _ => {}
    }

    match (lhs.maybe_func(), rhs.maybe_func()) {
        (Some((lhs_params, lhs_ret)), Some((rhs_params, rhs_ret))) => {
            let mut lhs = lhs_params.iter().collect::<Vec<_>>();
            lhs.push(lhs_ret);
            let mut rhs = rhs_params.iter().collect::<Vec<_>>();
            rhs.push(rhs_ret);
            return mgu_ref_slices(&lhs[..], &rhs[..], subst, synonyms);
        }
        _ => {}
    }

    match (lhs.maybe_tuple(), rhs.maybe_tuple()) {
        (Some(lhs_tys), Some(rhs_tys)) => {
            return mgu_slices(&lhs_tys, &rhs_tys, subst, synonyms);
        }
        _ => {}
    }

    Err(UnificationError::TypeMismatch(lhs.clone(), rhs.clone()))
}

pub fn mgu_type_var<T, V>(
    tyvar: &V,
    ty: &T,
    subst: &Subst<V, T>,
    synonyms: &OrderedTypeSynonyms<T, V>,
) -> Result<(bool, Subst<V, T>), UnificationError<T, V>>
where
    T: Ty<V>,
    V: TyVar,
{
    log::debug!("[mgu_type_var] tyvar={:?}, ty={:?}", tyvar, ty);
    match subst.get(tyvar) {
        Some(other_ty) => {
            log::debug!("[mgu_type_var] in subst: {:?} => {:?}", tyvar, other_ty);
            match mgu_with_synonyms(ty, other_ty, subst, synonyms) {
                Ok((true, mut subst)) => {
                    let mut a = ty.clone();
                    let mut b = other_ty.clone();
                    a.apply_subst(&subst);
                    b.apply_subst(&subst);
                    match a.eq_with_synonyms(&b, synonyms) {
                        Some(ty) => {
                            subst.remove(&tyvar);
                            subst.union(Subst::single(tyvar.clone(), ty));
                            log::debug!(
                                "[mgu_type_var] (after eq_with_synonyms) returning subst: {:?}",
                                subst
                            );
                            Ok((true, subst))
                        }
                        _ => Err(UnificationError::TypeMismatch(a, b)),
                    }
                }
                result => {
                    log::debug!("[mgu_type_var] result => {:?}", result);
                    result
                }
            }
        }
        _ => {
            let mut ty = ty.clone();
            ty.apply_subst(&subst);

            if let Some(other_tyvar) = ty.maybe_var() {
                if tyvar == other_tyvar {
                    log::debug!(
                        "[mgu_type_var] ignore equal type vars: {:?} == {:?}",
                        tyvar,
                        other_tyvar
                    );
                    return Ok((false, subst.clone()));
                }
            }

            let freevars = ty.free_vars();
            if freevars.contains(&&tyvar) {
                Err(UnificationError::InfiniteType(tyvar.clone()))
            } else {
                let mut subst = subst.clone();
                subst.union(Subst::single(tyvar.clone(), ty));
                log::debug!("[mgu_type_var] returning substitution: {:?}", subst,);
                Ok((false, subst))
            }
        }
    }
}

pub fn mgu_slices<T, V>(
    lhs: &[T],
    rhs: &[T],
    subst: &Subst<V, T>,
    synonyms: &OrderedTypeSynonyms<T, V>,
) -> Result<(bool, Subst<V, T>), UnificationError<T, V>>
where
    T: Ty<V>,
    V: TyVar,
{
    if lhs.len() != rhs.len() {
        return Err(UnificationError::TypeMismatch(
            T::tuple(lhs.into_iter().map(|t| t.clone()).collect()),
            T::tuple(rhs.into_iter().map(|t| t.clone()).collect()),
        ));
    }

    let mut changed = false;
    let mut subst = subst.clone();
    log::debug!("[mgu_slices] lhs={:?}, rhs={:?}", lhs, rhs);
    for (lhs, rhs) in lhs.iter().zip(rhs) {
        let (changed_, subst_) = mgu_with_synonyms(lhs, rhs, &subst, synonyms)?;
        changed = changed || changed_;
        subst = subst_.clone();
    }
    log::debug!(
        "[mgu_slices] returning subst (changed={}): {:?}",
        changed,
        subst
    );
    Ok((changed, subst))
}

pub fn mgu_ref_slices<T, V>(
    lhs: &[&T],
    rhs: &[&T],
    subst: &Subst<V, T>,
    synonyms: &OrderedTypeSynonyms<T, V>,
) -> Result<(bool, Subst<V, T>), UnificationError<T, V>>
where
    T: Ty<V>,
    V: TyVar,
{
    if lhs.len() != rhs.len() {
        return Err(UnificationError::TypeMismatch(
            T::tuple(lhs.into_iter().map(|&t| t.clone()).collect()),
            T::tuple(rhs.into_iter().map(|&t| t.clone()).collect()),
        ));
    }

    let mut subst = subst.clone();
    let mut changed = false;
    log::debug!("[mgu_ref_slices] lhs={:?}, rhs={:?}", lhs, rhs);
    for (&lhs, &rhs) in lhs.iter().zip(rhs) {
        let (changed_, subst_) = mgu_with_synonyms(lhs, rhs, &subst, synonyms)?;
        changed = changed || changed_;
        subst = subst_.clone();
    }
    log::debug!(
        "[mgu_ref_slices] returning subst (changed={}): {:?}",
        changed,
        subst
    );
    Ok((changed, subst))
}
