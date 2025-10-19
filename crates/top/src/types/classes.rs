use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::FromStr,
};

use serde::{Deserialize, Serialize};

use crate::{mgu_ref_slices, TyVar};

use super::{mgu_with_synonyms, OrderedTypeSynonyms, ShowQualifiers, Subst, Substitutable, Ty};

pub trait Entailment<Other, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn entails(
        &self,
        other: &Other,
        synonyms: &OrderedTypeSynonyms<T, V>,
        class_env: &ClassEnv<T, V>,
    ) -> bool;
}

#[derive(Default, Clone)]
pub struct ClassEnv<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    classes: HashMap<String, Class<T, V>>,
    record_classes: HashMap<String, Vec<Predicate<T, V>>>,
}

// impl<T, V> Deref for ClassEnv<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     type Target = HashMap<String, Class<T, V>>;

//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }

// impl<T, V> DerefMut for ClassEnv<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         &mut self.0
//     }
// }

// impl<T, V> IntoIterator for ClassEnv<T, V>
// where
//     T: Ty<V>,
//     V: TyVar,
// {
//     type Item = (String, Class<T, V>);
//     type IntoIter = <HashMap<String, Class<T, V>> as IntoIterator>::IntoIter;

//     fn into_iter(self) -> Self::IntoIter {
//         self.0.into_iter()
//     }
// }

impl<T, V> Debug for ClassEnv<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ClassEnv")
            .field("classes", &self.classes)
            .field("record_classes", &self.record_classes)
            .finish()
    }
}

impl<T, V> ClassEnv<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new() -> Self {
        ClassEnv {
            classes: HashMap::new(),
            record_classes: HashMap::new(),
        }
    }

    pub fn extend(&mut self, other: ClassEnv<T, V>) {
        self.classes.extend(other.classes);
        self.record_classes.extend(other.record_classes);
    }

    pub fn add_class(&mut self, path: String, class: Class<T, V>) {
        self.classes.insert(path, class);
    }

    pub fn add_record_class(&mut self, path: String, predicate: Predicate<T, V>) {
        self.record_classes
            .entry(path)
            .or_insert_with(Vec::new)
            .push(predicate);
    }

    pub fn superclasses(&self, class_name: &str) -> Option<&Vec<String>> {
        self.classes
            .get(class_name)
            .map(|class| &class.superclasses)
    }

    pub fn instances(&self, class_name: &str) -> Option<&Vec<Instance<T, V>>> {
        self.classes.get(class_name).map(|class| &class.instances)
    }

    pub fn record_types(&self, field: &str) -> Option<&Vec<Predicate<T, V>>> {
        self.record_classes.get(field)
    }

    pub fn by_superclass(&self, predicate: &Predicate<T, V>) -> Vec<Predicate<T, V>> {
        match predicate {
            Predicate::Class(name, ty, _) => {
                let mut result = vec![predicate.clone()];

                for superclass in self.superclasses(name).unwrap_or(&vec![]) {
                    let pred = Predicate::class(superclass.clone(), ty.clone());
                    result.extend(self.by_superclass(&pred));
                }

                result
            }
            _ => vec![],
        }
    }

    pub fn by_instance(
        &self,
        predicate: &Predicate<T, V>,
        synonyms: &OrderedTypeSynonyms<T, V>,
    ) -> Option<Vec<Predicate<T, V>>>
    where
        V: Display,
        <V as FromStr>::Err: Debug,
    {
        log::debug!("by_instance: predicate = {}", predicate);
        match predicate {
            Predicate::Class(class_name, _, _) => self
                .instances(class_name)?
                .into_iter()
                .find_map(|instance| {
                    let subst = predicate.match_with(&instance.head, synonyms)?;
                    let mut predicates = instance.predicates.clone();
                    predicates.apply_subst(&subst);
                    Some(predicates)
                })
                .map(|preds| preds.into()),
            Predicate::HasField(_, field_name, _, _) => self
                .record_types(field_name)?
                .into_iter()
                .find_map(|field_predicate| {
                    predicate.match_with(field_predicate, synonyms)?;
                    Some(vec![])
                })
                .map(|preds| preds.into()),
        }
    }

    pub fn superclass_entails(
        &self,
        predicates: &Vec<&Predicate<T, V>>,
        predicate: &Predicate<T, V>,
    ) -> bool {
        predicates
            .iter()
            .map(|pred| self.by_superclass(pred))
            .any(|superclasses| superclasses.contains(predicate))
    }
}

#[derive(Debug, Clone)]
pub struct Class<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub superclasses: Vec<String>,
    pub instances: Vec<Instance<T, V>>,
}

impl<T, V> Class<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new(superclasses: Vec<String>, instances: Vec<Instance<T, V>>) -> Self {
        Class {
            superclasses,
            instances,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Instance<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub head: Predicate<T, V>,
    pub predicates: Predicates<T, V>,
}

impl<T, V> Instance<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new(head: Predicate<T, V>, predicates: Predicates<T, V>) -> Self {
        Instance { head, predicates }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Predicate<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    Class(String, T, PhantomData<V>),
    HasField(T, String, T, PhantomData<V>),
}

impl<T, V> Debug for Predicate<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Class(name, ty, _) => f
                .debug_struct("Class")
                .field("name", name)
                .field("ty", ty)
                .finish(),
            Self::HasField(ty, field, field_ty, _) => f
                .debug_struct("HasField")
                .field("ty", ty)
                .field("field", field)
                .field("field_ty", field_ty)
                .finish(),
        }
    }
}

impl<T, V> Display for Predicate<T, V>
where
    T: Ty<V> + Display,
    V: TyVar + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Predicate::Class(name, ty, _) => write!(f, "{}[{}]", name, ty),
            Predicate::HasField(ty, name, field, _) => {
                write!(f, "{}::{} : {}", ty, name, field)
            }
        }
    }
}

impl<T, V> ShowQualifiers for Predicate<T, V>
where
    T: Ty<V> + Display,
    V: TyVar + Display,
{
    fn show_qualifiers(&self) -> Vec<String> {
        vec![self.to_string()]
    }
}

impl<T, V> Substitutable<V, T> for Predicate<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        match self {
            Predicate::Class(_, ty, _) => {
                ty.apply_subst(subst);
            }
            Predicate::HasField(ty, _, field, _) => {
                ty.apply_subst(subst);
                field.apply_subst(subst);
            }
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        match self {
            Predicate::Class(_, ty, _) => {
                ty.apply_subst_all(subst);
            }
            Predicate::HasField(ty, _, field, _) => {
                ty.apply_subst_all(subst);
                field.apply_subst_all(subst);
            }
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match self {
            Predicate::Class(_, ty, _) => ty.free_vars(),
            Predicate::HasField(ty, _, field, _) => ty
                .free_vars()
                .into_iter()
                .chain(field.free_vars())
                .collect(),
        }
    }
}

impl<T, V> Entailment<Predicate<T, V>, T, V> for Vec<&Predicate<T, V>>
where
    T: Ty<V>,
    V: TyVar + Display,
    <V as FromStr>::Err: Debug,
{
    fn entails(
        &self,
        predicate: &Predicate<T, V>,
        synonyms: &OrderedTypeSynonyms<T, V>,
        class_env: &ClassEnv<T, V>,
    ) -> bool {
        class_env.superclass_entails(self, predicate)
            || match class_env.by_instance(predicate, synonyms) {
                Some(qs) => qs.iter().all(|q| self.entails(q, synonyms, class_env)),
                None => false,
            }
    }
}

impl<T, V> Entailment<Vec<Predicate<T, V>>, T, V> for Vec<&Predicate<T, V>>
where
    T: Ty<V>,
    V: TyVar + Display,
    <V as FromStr>::Err: Debug,
{
    fn entails(
        &self,
        predicates: &Vec<Predicate<T, V>>,
        synonyms: &OrderedTypeSynonyms<T, V>,
        class_env: &ClassEnv<T, V>,
    ) -> bool {
        predicates
            .iter()
            .all(|p| self.entails(p, synonyms, class_env))
    }
}

impl<T, V> Predicate<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn class(name: String, ty: T) -> Self {
        Predicate::Class(name, ty, PhantomData)
    }

    pub fn has_field(ty: T, name: String, field: T) -> Self {
        Predicate::HasField(ty, name, field, PhantomData)
    }

    pub fn is_record_qualifier(&self) -> bool {
        matches!(self, Predicate::HasField(..))
    }

    pub fn in_head_normal_form(&self) -> bool {
        match self {
            Predicate::Class(_, ty, _) => ty.in_head_normal_form(),
            Predicate::HasField(ty, _, field_ty, _) => {
                ty.in_head_normal_form() || field_ty.in_head_normal_form()
            }
        }
    }

    pub fn match_with(
        &self,
        other: &Predicate<T, V>,
        synonyms: &OrderedTypeSynonyms<T, V>,
    ) -> Option<Subst<V, T>>
    where
        V: Display,
        <V as FromStr>::Err: Debug,
    {
        match (self, other) {
            (Predicate::Class(name1, lhs, _), Predicate::Class(name2, rhs, _))
                if name1 == name2 =>
            {
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
            (
                Predicate::HasField(lhs_ty, lhs_field, lhs_field_ty, _),
                Predicate::HasField(rhs_ty, rhs_field, rhs_field_ty, _),
            ) if lhs_field == rhs_field => {
                match mgu_ref_slices(
                    &[lhs_ty, lhs_field_ty],
                    &[rhs_ty, rhs_field_ty],
                    &Subst::new(),
                    synonyms,
                ) {
                    Ok((_, subst)) => Some(subst),
                    Err(_) => None,
                }
            }
            _ => None,
        }
    }
}

#[derive(Default, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Predicates<T, V>(Vec<Predicate<T, V>>)
where
    T: Ty<V>,
    V: TyVar;

impl<T, V> Deref for Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Target = Vec<Predicate<T, V>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, V> DerefMut for Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, V> Debug for Predicates<T, V>
where
    T: Debug + Ty<V>,
    V: Debug + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T, V> Display for Predicates<T, V>
where
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return write!(f, "[]");
        }

        write!(f, "[")?;
        for (i, pred) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", pred)?;
        }
        write!(f, "]")
    }
}

impl<'a, T, V> IntoIterator for &'a Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Item = &'a Predicate<T, V>;
    type IntoIter = <&'a Vec<Predicate<T, V>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T, V> IntoIterator for &'a mut Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Item = &'a mut Predicate<T, V>;
    type IntoIter = <&'a mut Vec<Predicate<T, V>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T, V> IntoIterator for Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Item = Predicate<T, V>;
    type IntoIter = <Vec<Predicate<T, V>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T, V> FromIterator<Predicate<T, V>> for Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Predicate<T, V>>,
    {
        Predicates(iter.into_iter().collect())
    }
}

impl<T, V> From<Vec<Predicate<T, V>>> for Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn from(predicates: Vec<Predicate<T, V>>) -> Self {
        Predicates(predicates)
    }
}

impl<T, V> Into<Vec<Predicate<T, V>>> for Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn into(self) -> Vec<Predicate<T, V>> {
        self.0
    }
}

impl<T, V> ShowQualifiers for Predicates<T, V>
where
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn show_qualifiers(&self) -> Vec<String> {
        self.iter().map(|pred| pred.to_string()).collect()
    }
}

impl<T, V> Substitutable<V, T> for Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        for pred in self.iter_mut() {
            pred.apply_subst(subst);
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        for pred in self.iter_mut() {
            pred.apply_subst_all(subst);
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        self.iter().flat_map(|pred| pred.free_vars()).collect()
    }
}

impl<T, V> Predicates<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new() -> Self {
        Predicates(vec![])
    }
}
