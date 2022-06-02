use std::ops::Deref;

use crate::util::Join;

use super::{HasTypes, OrderedTypeSynonyms, Subst, Substitutable};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ty {
    Var(u32),
    Const(String),
    Tuple(Vec<Ty>),
    App(Box<Ty>, Box<Ty>),
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Ty::Var(id) => write!(f, "?{}", id),
            Ty::Const(name) => write!(f, "{}", name),
            Ty::Tuple(tys) => write!(f, "({})", tys.join(", ")),
            Ty::App(lhs, rhs) => write!(f, "{} {}", lhs, rhs),
        }
    }
}

impl HasTypes for Ty {
    fn get_types(&self) -> Vec<&Ty> {
        vec![self]
    }

    fn change_types(&mut self, f: &impl FnMut(&mut Ty) -> ()) {
        match self {
            Ty::Var(_) => (),
            Ty::Const(_) => (),
            Ty::Tuple(tys) => tys.change_types(f),
            Ty::App(lhs, rhs) => {
                lhs.change_types(f);
                rhs.change_types(f);
            }
        }
    }
}

impl Substitutable for Ty {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Ty::Var(var) => {
                if let Some(ty) = subst.lookup_var(*var) {
                    *self = ty.clone();
                }
            }
            Ty::Const(_) => (),
            Ty::Tuple(tys) => tys.apply_subst(subst),
            Ty::App(lhs, rhs) => {
                lhs.apply_subst(subst);
                rhs.apply_subst(subst);
            }
        }
    }

    fn free_vars(&self) -> Vec<u32> {
        match self {
            Ty::Var(var) => vec![*var],
            Ty::Const(_) => vec![],
            Ty::Tuple(tys) => tys.free_vars(),
            Ty::App(lhs, rhs) => lhs.free_vars().into_iter().chain(rhs.free_vars()).collect(),
        }
    }
}

impl Ty {
    pub fn skolem(id: u32) -> Self {
        Ty::Const(format!("#{}", id))
    }

    pub fn new(name: &str) -> Self {
        Ty::Const(name.to_string())
    }

    pub fn arrow(lhs: Self, rhs: Self) -> Self {
        Ty::App(
            Box::new(Ty::Const("->".to_string())),
            Box::new(Ty::App(Box::new(lhs), Box::new(rhs))),
        )
    }

    pub fn func(param_tys: Vec<Ty>, ret_ty: Ty) -> Self {
        let mut func = ret_ty;

        for param_ty in param_tys.into_iter().rev() {
            func = Ty::arrow(param_ty, func);
        }

        func
    }

    pub fn is_tyvar(&self) -> bool {
        matches!(self, Ty::Var(_))
    }

    pub fn is_const(&self) -> bool {
        matches!(self, Ty::Const(_))
    }

    pub fn is_app(&self) -> bool {
        matches!(self, Ty::App(_, _))
    }

    pub fn is_func(&self) -> bool {
        matches!(
            self,
            Ty::App(lhs, rhs) if lhs.name() == "->" && rhs.is_app(),
        )
    }

    pub fn in_head_normal_form(&self) -> bool {
        match &self {
            Ty::Var(_) => true,
            Ty::Const(_) => false,
            Ty::Tuple(tys) => tys.iter().all(|ty| ty.in_head_normal_form()),
            Ty::App(ty, _) => ty.in_head_normal_form(),
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Ty::Const(name) => name,
            _ => {
                panic!("type has no name")
            }
        }
    }

    pub fn variables(&self) -> Vec<u32> {
        match self {
            Ty::Var(id) => vec![*id],
            Ty::Const(_) => vec![],
            Ty::Tuple(tys) => tys.iter().flat_map(|ty| ty.variables()).collect(),
            Ty::App(lhs, rhs) => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars.sort();
                vars.dedup();
                vars
            }
        }
    }

    pub fn constants(&self) -> Vec<String> {
        match self {
            Ty::Var(_) => vec![],
            Ty::Const(name) => vec![name.clone()],
            Ty::Tuple(tys) => tys.iter().flat_map(|ty| ty.constants()).collect(),
            Ty::App(lhs, rhs) => {
                let mut consts = lhs.constants();
                consts.extend(rhs.constants());
                consts.sort();
                consts.dedup();
                consts
            }
        }
    }

    pub fn left_spine(&self) -> (&Ty, Vec<&Ty>) {
        self.left_spine_rec(vec![])
    }

    fn left_spine_rec<'a>(&'a self, tys: Vec<&'a Ty>) -> (&'a Ty, Vec<&'a Ty>) {
        if let Ty::App(lhs, rhs) = self {
            lhs.left_spine_rec(std::iter::once(rhs.deref()).chain(tys).collect())
        } else {
            (self, tys)
        }
    }

    pub fn eq_with_synonyms(&self, other: &Ty, synonyms: &OrderedTypeSynonyms) -> Option<Ty> {
        let (lhs, lhs_tys) = self.left_spine();
        let (rhs, rhs_tys) = other.left_spine();
        match ((lhs, &lhs_tys[..]), (rhs, &rhs_tys[..])) {
            ((Ty::Var(_), &[]), (Ty::Var(_), &[])) => Some(self.clone()),
            ((Ty::Var(i), ss), (Ty::Var(_), tt)) => {
                if ss.len() != tt.len() {
                    None
                } else {
                    Some(
                        ss.iter()
                            .zip(tt.iter())
                            .flat_map(|(s, t)| s.eq_with_synonyms(t, synonyms))
                            .fold(Ty::Var(*i), |acc, ty| Ty::App(Box::new(acc), Box::new(ty))),
                    )
                }
            }
            ((Ty::Const(s), ss), (Ty::Const(t), tt))
                if s == t && !synonyms.is_phantom_synonym(s) =>
            {
                Some(
                    ss.iter()
                        .zip(tt.iter())
                        .flat_map(|(s, t)| s.eq_with_synonyms(t, synonyms))
                        .fold(Ty::Const(s.clone()), |acc, ty| {
                            Ty::App(Box::new(acc), Box::new(ty))
                        }),
                )
            }
            ((Ty::Const(_), _), (Ty::Const(_), _)) => synonyms
                .expand_ordered(lhs, rhs)
                .and_then(|(a, b)| a.eq_with_synonyms(b, synonyms)),
            _ => None,
        }
    }

    pub fn freeze_vars(&self) -> Ty {
        match self {
            Ty::Var(i) => Ty::Const(format!("_{}", i)),
            Ty::Const(_) => self.clone(),
            Ty::Tuple(tys) => Ty::Tuple(tys.iter().map(|ty| ty.freeze_vars()).collect()),
            Ty::App(left, right) => {
                Ty::App(Box::new(left.freeze_vars()), Box::new(right.freeze_vars()))
            }
        }
    }

    pub fn unfreeze_vars(&self) -> Ty {
        match self {
            Ty::Var(i) => Ty::Var(*i),
            Ty::Const(s) => {
                if s.starts_with('_') {
                    let chars = s.chars().skip(1).collect::<Vec<_>>();
                    if chars.len() != 0 && chars.iter().all(|c| c.is_ascii_digit()) {
                        let s = chars.iter().collect::<String>();
                        return Ty::Var(s.parse().unwrap());
                    }
                }
                self.clone()
            }
            Ty::Tuple(tys) => Ty::Tuple(tys.iter().map(|ty| ty.unfreeze_vars()).collect()),
            Ty::App(left, right) => Ty::App(
                Box::new(left.unfreeze_vars()),
                Box::new(right.unfreeze_vars()),
            ),
        }
    }
}
