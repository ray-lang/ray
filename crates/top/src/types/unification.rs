use super::{OrderedTypeSynonyms, Subst, Substitutable, Ty};

#[derive(Debug, PartialEq, Eq)]
pub enum UnificationError {
    TypeMismatch(Ty, Ty),
    ConstantMismatch(String, String),
    InfiniteType(u32),
}

impl std::fmt::Display for UnificationError {
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

pub fn mgu_with_synonyms(
    lhs: &Ty,
    rhs: &Ty,
    subst: &Subst,
    synonyms: &OrderedTypeSynonyms,
) -> Result<(bool, Subst), UnificationError> {
    let (lhs_lsp, lhs_tys) = lhs.left_spine();
    let (rhs_lsp, rhs_tys) = rhs.left_spine();

    match ((lhs_lsp, &lhs_tys[..]), (rhs_lsp, &rhs_tys[..])) {
        ((Ty::Var(tyvar), &[]), _) => mgu_type_var(*tyvar, rhs, subst, synonyms),
        (_, (Ty::Var(tyvar), &[])) => mgu_type_var(*tyvar, lhs, subst, synonyms),
        ((Ty::Const(a), lhs), (Ty::Const(b), rhs))
            if a == b && !synonyms.is_phantom_synonym(&a) =>
        {
            mgu_slices(lhs, rhs, synonyms)
        }
        ((Ty::Const(s), _), (Ty::Const(t), _)) => match synonyms.expand_ordered(lhs, rhs) {
            Some((a, b)) => match mgu_with_synonyms(a, b, subst, synonyms) {
                Ok((_, subst)) => Ok((true, subst)),
                Err(e) => Err(e),
            },
            _ => Err(UnificationError::ConstantMismatch(s.clone(), t.clone())),
        },
        _ => {
            if let (Ty::App(l1, r1), Ty::App(l2, r2)) = (lhs, rhs) {
                let lhs = &[l1.as_ref(), r1.as_ref()];
                let rhs = &[l2.as_ref(), r2.as_ref()];
                mgu_slices(lhs, rhs, synonyms)
            } else {
                Err(UnificationError::TypeMismatch(lhs.clone(), rhs.clone()))
            }
        }
    }
}

pub fn mgu_type_var(
    tyvar: u32,
    ty: &Ty,
    subst: &Subst,
    synonyms: &OrderedTypeSynonyms,
) -> Result<(bool, Subst), UnificationError> {
    match subst.get(&tyvar) {
        Some(other_ty) => match mgu_with_synonyms(ty, other_ty, subst, synonyms) {
            Ok((true, mut subst)) => {
                let mut a = ty.clone();
                let mut b = other_ty.clone();
                a.apply_subst(&subst);
                b.apply_subst(&subst);
                match a.eq_with_synonyms(&b, synonyms) {
                    Some(ty) => {
                        subst.insert(tyvar, ty);
                        Ok((true, subst))
                    }
                    _ => Err(UnificationError::TypeMismatch(a, b)),
                }
            }
            result => result,
        },
        _ => {
            let mut ty = ty.clone();
            ty.apply_subst(&subst);

            match ty {
                Ty::Var(other_tyvar) if tyvar == other_tyvar => Ok((false, subst.clone())),
                _ => {
                    let freevars = ty.free_vars();
                    if freevars.contains(&tyvar) {
                        Err(UnificationError::InfiniteType(tyvar))
                    } else {
                        let mut subst = subst.clone();
                        subst.insert(tyvar, ty);
                        Ok((false, subst))
                    }
                }
            }
        }
    }
}

pub fn mgu_slices(
    lhs: &[&Ty],
    rhs: &[&Ty],
    synonyms: &OrderedTypeSynonyms,
) -> Result<(bool, Subst), UnificationError> {
    if lhs.len() != rhs.len() {
        return Err(UnificationError::TypeMismatch(
            Ty::Tuple(lhs.into_iter().map(|&t| t.clone()).collect()),
            Ty::Tuple(rhs.into_iter().map(|&t| t.clone()).collect()),
        ));
    }

    let mut subst = Subst::new();
    let mut changed = false;
    for (lhs, rhs) in lhs.iter().zip(rhs) {
        let (changed_, subst_) = mgu_with_synonyms(lhs, rhs, &subst, synonyms)?;
        changed = changed || changed_;
        subst = subst_.clone();
    }
    Ok((changed, subst))
}
