use std::collections::HashMap;

use crate::util::DisplayableVec;

use super::{
    mgu_with_synonyms, ClassEnv, Entailment, ForAll, OrderedTypeSynonyms, Predicate, Qualification,
    ShowQualifiers, ShowQuantorOptions, ShowQuantors, Subst, Substitutable, Ty,
};

pub type QualifiedTy = Qualification<Vec<Predicate>, Ty>;

pub type TyScheme = ForAll<QualifiedTy>;

impl Into<TyScheme> for QualifiedTy {
    fn into(self) -> TyScheme {
        TyScheme::new(self)
    }
}

impl Into<TyScheme> for Ty {
    fn into(self) -> TyScheme {
        TyScheme::new(QualifiedTy::new(vec![], self))
    }
}

impl TyScheme {
    pub fn new_scheme(mono_tys: Vec<u32>, predicates: Vec<Predicate>, ty: Ty) -> Self {
        let vars = ty
            .free_vars()
            .into_iter()
            .filter(|var| !mono_tys.contains(var))
            .collect::<Vec<_>>();
        let predicates = predicates
            .into_iter()
            .filter(|pred| {
                let freevars = pred.free_vars();
                freevars.iter().any(|var| vars.contains(var))
            })
            .collect();

        Self {
            vars,
            quantor_map: HashMap::new(),
            ty: QualifiedTy::new(predicates, ty),
        }
    }

    pub fn is_overloaded(&self) -> bool {
        !self.unquantified().qualifiers().is_empty()
    }

    pub fn generic_instance_of(
        &self,
        other_scheme: &TyScheme,
        synonyms: &OrderedTypeSynonyms,
        class_env: &ClassEnv,
    ) -> bool {
        let mut s1 = self.clone();
        s1.skolemize_free_vars();
        let mut s2 = other_scheme.clone();
        s2.skolemize_free_vars();

        let subst = s1
            .quantifiers()
            .iter()
            .cloned()
            .zip((0u32..).map(|i| Ty::Const(format!("+{}", i))))
            .collect::<Subst>();

        let mut s1 = s1.unquantify();
        s1.apply_subst(&subst);
        let (preds1, ty1) = s1.split();
        let (_, s2) = s2.instantiate(1000000);
        let (mut preds2, ty2) = s2.split();

        match mgu_with_synonyms(&ty1, &ty2, &Subst::new(), synonyms) {
            Ok((_, subst)) => {
                preds2.apply_subst(&subst);
                let preds2 = preds2.iter().collect::<Vec<_>>();
                preds2.entails(&preds1, synonyms, class_env)
            }
            Err(_) => false,
        }
    }
}

pub type Scheme<T> = ForAll<Qualification<T, Ty>>;

#[derive(Debug, Clone)]
pub enum Sigma<T> {
    Var(u32),
    Scheme(Scheme<T>),
}

impl<T> std::fmt::Display for Sigma<T>
where
    T: std::fmt::Display + ShowQualifiers + Substitutable,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Sigma::Var(var) => write!(f, "$s{}", var),
            Sigma::Scheme(scheme) => write!(f, "{}", scheme),
        }
    }
}

impl<T> ShowQuantors for Sigma<T>
where
    T: Clone + std::fmt::Display + Substitutable + ShowQualifiers,
{
    fn show_quantors_without(&self, options: &ShowQuantorOptions) -> String
    where
        Self: std::fmt::Display,
    {
        match self {
            Sigma::Var(_) => self.to_string(),
            Sigma::Scheme(ts) => ts.show_quantors_without(options),
        }
    }
}

impl<T> Substitutable for Sigma<T>
where
    T: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Sigma::Var(_) => {}
            Sigma::Scheme(scheme) => scheme.apply_subst(subst),
        }
    }

    fn free_vars(&self) -> Vec<u32> {
        match self {
            Sigma::Var(_) => vec![],
            Sigma::Scheme(scheme) => scheme.free_vars(),
        }
    }
}

impl<T> Sigma<Vec<T>>
where
    T: std::fmt::Display + Clone,
{
    pub fn displayable(&self) -> Sigma<DisplayableVec<T>> {
        match self {
            Sigma::Var(var) => Sigma::Var(*var),
            Sigma::Scheme(scheme) => {
                let ForAll {
                    vars,
                    quantor_map,
                    ty,
                } = scheme.clone();
                Sigma::Scheme(ForAll {
                    vars,
                    quantor_map,
                    ty: ty.into(),
                })
            }
        }
    }
}
