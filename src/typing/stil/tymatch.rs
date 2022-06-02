use crate::typing::{predicate::TyPredicate, ty::Ty, Subst};

pub trait TyMatch {
    fn match_tys(&self, other: &Self) -> Result<Subst, String>;
}

impl TyMatch for Ty {
    fn match_tys(&self, other: &Ty) -> Result<Subst, String> {
        Ok(match (self, other) {
            (Ty::Never, Ty::Never) | (Ty::Any, Ty::Any) => Subst::new(),
            (Ty::Var(s), Ty::Var(t)) => Subst::one(s.clone(), Ty::Var(t.clone())),
            (Ty::Tuple(tys1), Ty::Tuple(tys2)) => {
                let mut sub = Subst::new();
                for (a, b) in tys1.iter().zip(tys2.iter()) {
                    if !sub.merge(a.match_tys(b)?) {
                        return Err(format!("types `{}` and `{}` cannot be merged", a, b));
                    }
                }

                sub
            }
            (Ty::Union(_), Ty::Union(_)) => todo!(),
            (Ty::Array(t, c1), Ty::Array(u, c2)) if c1 == c2 => t.match_tys(u)?,
            (Ty::Func(p1, r1), Ty::Func(p2, r2)) if p1.len() == p2.len() => {
                let mut sub = Subst::new();
                for (a, b) in p1.iter().zip(p2.iter()) {
                    if !sub.merge(a.match_tys(b)?) {
                        return Err(format!("types `{}` and `{}` cannot be merged", a, b));
                    }
                }

                sub.merge(r1.match_tys(r2)?);
                sub
            }
            (Ty::Projection(c1, tys1), Ty::Projection(c2, tys2))
                if c1 == c2 && tys1.len() == tys2.len() =>
            {
                let mut sub = Subst::new();
                for (a, b) in tys1.iter().zip(tys2.iter()) {
                    if !sub.merge(a.match_tys(b)?) {
                        return Err(format!("types `{}` and `{}` cannot be merged", a, b));
                    }
                }

                sub
            }
            (Ty::Ptr(t), Ty::Ptr(u))
            | (Ty::Qualified(_, t), Ty::Qualified(_, u))
            | (Ty::All(_, t), Ty::All(_, u)) => t.match_tys(u)?,
            _ => return Err(format!("types `{}` and `{}` do not match", self, other)),
        })
    }
}

impl TyMatch for TyPredicate {
    fn match_tys(&self, other: &TyPredicate) -> Result<Subst, String> {
        match (self, other) {
            (TyPredicate::Trait(a), TyPredicate::Trait(b))
            | (TyPredicate::Literal(a, _), TyPredicate::Literal(b, _))
            | (TyPredicate::HasMember(a, _, _), TyPredicate::HasMember(b, _, _)) => a.match_tys(a),
            _ => Err(format!(
                "predicates `{}` and `{}` do not match",
                self, other
            )),
        }
    }
}
