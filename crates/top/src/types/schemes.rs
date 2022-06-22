use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    str::FromStr,
};

use serde::{Deserialize, Serialize};

use crate::{Predicates, TyVar};

use super::{
    mgu_with_synonyms, ClassEnv, Entailment, ForAll, OrderedTypeSynonyms, Predicate, Qualification,
    ShowQualifiers, ShowQuantorOptions, ShowQuantors, Subst, Substitutable, Ty,
};

// pub type QualifiedTy<T, V> = Qualification<Predicates<T, V>, T>;

// #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
// pub enum TyScheme<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     Poly(ForAll<QualifiedTy<T, V>, T, V>),
//     Mono(T),
// }

// impl<T, V> Into<TyScheme<T, V>> for QualifiedTy<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     fn into(self) -> TyScheme<T, V> {
//         TyScheme::Poly(ForAll::new(self))
//     }
// }

// impl<T, V> From<T> for TyScheme<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     fn from(t: T) -> Self {
//         TyScheme::Mono(t)
//     }
// }

// impl<T, V> Display for TyScheme<T, V>
// where
//     T: Display + Ty<V>,
//     V: Display + TyVar,
// {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             TyScheme::Poly(poly) => write!(f, "{}", poly.displayable()),
//             TyScheme::Mono(mono) => write!(f, "{}", mono),
//         }
//     }
// }

// impl<T, V> Substitutable<V, T> for TyScheme<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     fn apply_subst(&mut self, subst: &Subst<V, T>) {
//         match self {
//             TyScheme::Poly(ty) => ty.apply_subst(subst),
//             TyScheme::Mono(ty) => ty.apply_subst(subst),
//         }
//     }

//     fn free_vars(&self) -> Vec<&V> {
//         match self {
//             TyScheme::Poly(ty) => ty.free_vars(),
//             TyScheme::Mono(ty) => ty.free_vars(),
//         }
//     }
// }

// impl<T, V> TyScheme<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     pub fn new_scheme(mono_tys: Vec<V>, predicates: Predicates<T, V>, ty: T) -> Self {
//         let vars = ty
//             .free_vars()
//             .into_iter()
//             .filter(|var| !mono_tys.contains(var))
//             .cloned()
//             .collect::<Vec<_>>();
//         let predicates = predicates
//             .into_iter()
//             .filter(|pred| {
//                 let freevars = pred.free_vars();
//                 freevars.iter().any(|var| vars.contains(var))
//             })
//             .collect();

//         if vars.is_empty() {
//             TyScheme::Mono(ty)
//         } else {
//             TyScheme::Poly(ForAll::new(QualifiedTy::new(predicates, ty)))
//         }
//     }

//     pub fn is_overloaded(&self) -> bool {
//         if let Some(qual_ty) = self.unquantified() {
//             !qual_ty.qualifiers().is_empty()
//         } else {
//             false
//         }
//     }

//     pub fn is_polymorphic(&self) -> bool {
//         matches!(self, TyScheme::Poly(_))
//     }

//     pub fn quantifiers(&self) -> Option<&Vec<V>> {
//         match self {
//             TyScheme::Poly(ty) => Some(&ty.quantifiers()),
//             TyScheme::Mono(_) => None,
//         }
//     }

//     pub fn unquantified(&self) -> Option<&QualifiedTy<T, V>> {
//         match self {
//             TyScheme::Poly(forall) => Some(forall.unquantified()),
//             TyScheme::Mono(_) => None,
//         }
//     }

//     pub fn unquantify(self) -> Option<QualifiedTy<T, V>> {
//         match self {
//             TyScheme::Poly(forall) => Some(forall.unquantify()),
//             TyScheme::Mono(_) => None,
//         }
//     }

//     pub fn instantiate(&self, n: u32) -> Option<(u32, QualifiedTy<T, V>)> {
//         match self {
//             TyScheme::Poly(forall) => Some(forall.clone().instantiate(n)),
//             TyScheme::Mono(_) => None,
//         }
//     }

//     pub fn generic_instance_of(
//         &self,
//         other_scheme: &TyScheme<T, V>,
//         synonyms: &OrderedTypeSynonyms<T, V>,
//         class_env: &ClassEnv<T, V>,
//     ) -> bool
//     where
//         V: Display,
//         <V as FromStr>::Err: Debug,
//     {
//         let mut s1 = self.clone();
//         s1.skolemize_free_vars();
//         let mut s2 = other_scheme.clone();
//         s2.skolemize_free_vars();

//         let quantifiers = match s1.quantifiers() {
//             Some(quantifiers) => quantifiers,
//             None => return false,
//         };

//         let subst = quantifiers
//             .iter()
//             .cloned()
//             .zip((0u32..).map(|i| T::new(&format!("+{}", i))))
//             .collect::<Subst<V, T>>();

//         let mut s1 = match s1.unquantify() {
//             Some(ty) => ty,
//             None => return false,
//         };
//         s1.apply_subst(&subst);
//         let (preds1, ty1) = s1.split();
//         let s2 = match s2.instantiate(1000000) {
//             Some((_, ty)) => ty,
//             None => return false,
//         };

//         let (mut preds2, ty2) = s2.split();

//         match mgu_with_synonyms(&ty1, &ty2, &Subst::new(), synonyms) {
//             Ok((_, subst)) => {
//                 preds2.apply_subst(&subst);
//                 let preds2 = preds2.iter().collect::<Vec<_>>();
//                 preds2.entails(&preds1, synonyms, class_env)
//             }
//             Err(_) => false,
//         }
//     }
// }

pub type Scheme<Q, T, V> = ForAll<Qualification<Q, T>, T, V>;
pub type SchemePredicates<T, V> = Scheme<Predicates<T, V>, T, V>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Sigma<Q, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    Var(V),
    Scheme(Scheme<Q, T, V>),
}

pub type SigmaPredicates<T, V> = Sigma<Predicates<T, V>, T, V>;

impl<Q, T, V> Display for Sigma<Q, T, V>
where
    Q: Display + Clone + ShowQualifiers + Substitutable<V, T>,
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Sigma::Var(var) => write!(f, "$s{}", var),
            Sigma::Scheme(scheme) => write!(f, "{}", scheme),
        }
    }
}

impl<Q, T, V> ShowQuantors for Sigma<Q, T, V>
where
    Q: Clone + Display + Substitutable<V, T> + ShowQualifiers,
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn show_quantors_without(&self, options: &ShowQuantorOptions) -> String
    where
        Self: Display,
    {
        match self {
            Sigma::Var(_) => self.to_string(),
            Sigma::Scheme(ts) => ts.show_quantors_without(options),
        }
    }
}

impl<Q, T, V> Substitutable<V, T> for Sigma<Q, T, V>
where
    Q: Substitutable<V, T>,
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        match self {
            Sigma::Var(v) => {
                todo!("v = {:?}", v);
            }
            Sigma::Scheme(scheme) => scheme.apply_subst(subst),
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        match self {
            Sigma::Var(v) => {
                todo!("v = {:?}", v);
            }
            Sigma::Scheme(scheme) => scheme.apply_subst_all(subst),
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match self {
            Sigma::Var(_) => vec![],
            Sigma::Scheme(scheme) => scheme.free_vars(),
        }
    }
}

// impl<Q, T, V> Sigma<Vec<Q>, T, V>
// where
//     Q: Display + Clone,
//     T: Ty<V>,
//     V: TyVar,
// {
//     pub fn displayable<'a>(&self) -> Sigma<DisplayableVec<'a, Q>, T, V> {
//         match self {
//             Sigma::Var(var) => Sigma::Var(var.clone()),
//             Sigma::Scheme(scheme) => {
//                 let ForAll { vars, ty, .. } = scheme.clone();
//                 Sigma::Scheme(ForAll {
//                     vars,
//                     ty: ty.into(),
//                     _phantom: PhantomData,
//                 })
//             }
//         }
//     }
// }

impl<T, V> Sigma<Predicates<T, V>, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn mono(ty: T) -> Self {
        Sigma::Scheme(ForAll::mono(Qualification::new(Predicates::new(), ty)))
    }
}
