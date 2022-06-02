use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use crate::util::DisplayableVec;

use super::{mgu_with_synonyms, OrderedTypeSynonyms, ShowQualifiers, Subst, Substitutable, Ty};

pub trait Entailment<Other> {
    fn entails(&self, other: &Other, synonyms: &OrderedTypeSynonyms, class_env: &ClassEnv) -> bool;
}

#[derive(Debug, Default, Clone)]
pub struct ClassEnv(HashMap<String, Class>);

impl Deref for ClassEnv {
    type Target = HashMap<String, Class>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ClassEnv {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl IntoIterator for ClassEnv {
    type Item = (String, Class);
    type IntoIter = <HashMap<String, Class> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl ClassEnv {
    pub fn new() -> Self {
        ClassEnv(HashMap::new())
    }

    pub fn superclasses(&self, class_name: &str) -> Option<&Vec<String>> {
        self.0.get(class_name).map(|class| &class.superclasses)
    }

    pub fn instances(&self, class_name: &str) -> Option<&Vec<Instance>> {
        self.0.get(class_name).map(|class| &class.instances)
    }

    pub fn by_superclass(&self, predicate: &Predicate) -> Vec<Predicate> {
        let (name, ty) = predicate.split_borrowed();
        let mut result = vec![predicate.clone()];

        for superclass in self.superclasses(name).unwrap_or(&vec![]) {
            let pred = Predicate::new(superclass, ty);
            result.extend(self.by_superclass(&pred));
        }

        result
    }

    pub fn by_instance(
        &self,
        predicate: &Predicate,
        synonyms: &OrderedTypeSynonyms,
    ) -> Option<Vec<Predicate>> {
        let (class_name, _) = predicate.split_borrowed();
        Some(
            self.instances(class_name)?
                .into_iter()
                .flat_map(|instance| {
                    let subst = instance.head.match_with(predicate, synonyms)?;
                    let mut predicates = instance.predicates.clone();
                    predicates.apply_subst(&subst);
                    Some(predicates)
                })
                .flatten()
                .collect(),
        )
    }

    pub fn superclass_entails(&self, predicates: &Vec<&Predicate>, predicate: &Predicate) -> bool {
        predicates
            .iter()
            .map(|pred| self.by_superclass(pred))
            .any(|superclasses| superclasses.contains(predicate))
    }
}

#[derive(Debug, Clone)]
pub struct Class {
    pub superclasses: Vec<String>,
    pub instances: Vec<Instance>,
}

#[derive(Debug, Clone)]
pub struct Instance {
    pub head: Predicate,
    pub predicates: Vec<Predicate>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub name: String,
    pub ty: Ty,
}

pub type Predicates = DisplayableVec<Predicate>;

impl std::fmt::Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} {}", self.name, self.ty)
    }
}

impl ShowQualifiers for Predicate {
    fn show_qualifiers(&self) -> Vec<String> {
        vec![self.to_string()]
    }
}

impl Substitutable for Predicate {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
    }

    fn free_vars(&self) -> Vec<u32> {
        self.ty.free_vars()
    }
}

impl Entailment<Predicate> for Vec<&Predicate> {
    fn entails(
        &self,
        predicate: &Predicate,
        synonyms: &OrderedTypeSynonyms,
        class_env: &ClassEnv,
    ) -> bool {
        class_env.superclass_entails(self, predicate)
            || match class_env.by_instance(predicate, synonyms) {
                Some(qs) => qs.iter().all(|q| self.entails(q, synonyms, class_env)),
                None => false,
            }
    }
}

impl Entailment<Vec<Predicate>> for Vec<&Predicate> {
    fn entails(
        &self,
        predicates: &Vec<Predicate>,
        synonyms: &OrderedTypeSynonyms,
        class_env: &ClassEnv,
    ) -> bool {
        predicates
            .iter()
            .all(|p| self.entails(p, synonyms, class_env))
    }
}

impl Predicate {
    pub fn new(name: &str, ty: &Ty) -> Self {
        Predicate {
            name: name.to_string(),
            ty: ty.clone(),
        }
    }

    pub fn in_head_normal_form(&self) -> bool {
        self.ty.in_head_normal_form()
    }

    pub fn split_borrowed(&self) -> (&String, &Ty) {
        let Predicate { name, ty } = self;
        (name, ty)
    }

    pub fn match_with(&self, other: &Predicate, synonyms: &OrderedTypeSynonyms) -> Option<Subst> {
        match (self.split_borrowed(), other.split_borrowed()) {
            ((name1, lhs), (name2, rhs)) if name1 == name2 => {
                let lhs = lhs.freeze_vars();
                match mgu_with_synonyms(&lhs, rhs, &Subst::new(), synonyms) {
                    Ok((_, mut subst)) => {
                        for (_, ty) in subst.iter_mut() {
                            *ty = ty.unfreeze_vars();
                        }
                        Some(subst)
                    }
                    Err(_) => None,
                }
            }
            _ => None,
        }
    }
}
