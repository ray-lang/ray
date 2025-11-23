use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::FromStr,
};

use serde::{Deserialize, Serialize};

use crate::{TyVar, mgu_ref_slices};

use super::{OrderedTypeSynonyms, ShowQualifiers, Subst, Substitutable, Ty};

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
    fn instantiate_super_params(
        param_vars: &[T],
        actual_args: &[T],
        mut template: Vec<T>,
    ) -> Option<Vec<T>> {
        if param_vars.len() != actual_args.len() {
            return None;
        }

        let mut subst = Subst::new();
        for (param, arg) in param_vars.iter().zip(actual_args) {
            if let Some(var) = param.maybe_var() {
                subst.insert(var.clone(), arg.clone());
            }
        }

        template.apply_subst(&subst);
        Some(template)
    }

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

    pub fn superclasses(&self, class_name: &str) -> Option<&Vec<(String, Vec<T>)>> {
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
            Predicate::Class(name, ty, params, _) => {
                let mut result = vec![predicate.clone()];

                if let Some(class) = self.classes.get(name) {
                    let mut actual_args = Vec::with_capacity(1 + params.len());
                    actual_args.push(ty.clone());
                    actual_args.extend(params.iter().cloned());

                    for (superclass, super_params) in &class.superclasses {
                        if let Some(instantiated_params) = ClassEnv::instantiate_super_params(
                            &class.param_vars,
                            &actual_args,
                            super_params.clone(),
                        ) {
                            let mut iter = instantiated_params.into_iter();
                            if let Some(base) = iter.next() {
                                let pred =
                                    Predicate::class(superclass.clone(), base, iter.collect());
                                result.extend(self.by_superclass(&pred));
                            }
                        }
                    }
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
    ) -> Option<Vec<(Subst<V, T>, Vec<Predicate<T, V>>)>>
    where
        V: Display,
        <V as FromStr>::Err: Debug,
    {
        log::debug!("by_instance: predicate = {}", predicate);
        match predicate {
            Predicate::Class(class_name, _, _, _) => {
                let mut candidates = vec![];
                for instance in self.instances(class_name)?.iter() {
                    log::debug!("by_instance: instance = {:?}", instance);
                    let Some(subst) = predicate.match_with(&instance.head, synonyms) else {
                        log::debug!(
                            "by_instance: predicates do not match: predicate={} & instance_head={}",
                            predicate,
                            instance.head
                        );
                        continue;
                    };
                    log::debug!("by_instance: subst = {:?}", subst);
                    let mut predicates = instance.predicates.clone();
                    log::debug!(
                        "by_instance: instance predicates (before apply_subst) = {:?}",
                        predicates
                    );
                    predicates.apply_subst(&subst);
                    log::debug!(
                        "by_instance: instance predicates (after apply_subst) = {:?}",
                        predicates
                    );

                    candidates.push((subst, predicates.into()));
                }

                if candidates.is_empty() {
                    return None;
                }

                Some(candidates)
            }

            Predicate::HasField(_, field_name, _, _) => {
                // HasField predicates are discharged via record_classes.
                // If any record predicate for this field name matches (using
                // match_with, which handles auto-deref for *T), we consider
                // the predicate solvable with no additional obligations.
                let record_preds = self.record_types(field_name)?;
                if record_preds
                    .iter()
                    .any(|rp| predicate.match_with(rp, synonyms).is_some())
                {
                    Some(vec![])
                } else {
                    None
                }
            }
            Predicate::Recv(..) => None,
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
    pub param_vars: Vec<T>,
    pub superclasses: Vec<(String, Vec<T>)>,
    pub instances: Vec<Instance<T, V>>,
}

impl<T, V> Class<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new(
        param_vars: Vec<T>,
        superclasses: Vec<(String, Vec<T>)>,
        instances: Vec<Instance<T, V>>,
    ) -> Self {
        Class {
            param_vars,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RecvKind {
    Value,
    Ref,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Predicate<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    Class(String, T, Vec<T>, PhantomData<V>),
    HasField(T, String, T, PhantomData<V>),
    Recv(RecvKind, T, T, PhantomData<V>),
}

impl<T, V> Debug for Predicate<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::Class(name, ty, params, _) => f
                .debug_struct("Class")
                .field("name", name)
                .field("ty", ty)
                .field("params", params)
                .finish(),
            Predicate::HasField(ty, field, field_ty, _) => f
                .debug_struct("HasField")
                .field("ty", ty)
                .field("field", field)
                .field("field_ty", field_ty)
                .finish(),
            Predicate::Recv(recv_kind, recv_ty, self_ty, _) => f
                .debug_struct("Recv")
                .field("kind", recv_kind)
                .field("recv_ty", recv_ty)
                .field("self_ty", self_ty)
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
            Predicate::Class(name, ty, params, _) => {
                let params = params
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let comma = if !params.is_empty() { ", " } else { "" };
                write!(f, "{}[{}{}{}]", name, ty, comma, params)
            }
            Predicate::HasField(ty, name, field, _) => {
                write!(f, "{}::{} : {}", ty, name, field)
            }
            Predicate::Recv(recv_kind, recv_ty, self_ty, _) => {
                write!(f, "recv({:?}, {}, {})", recv_kind, recv_ty, self_ty)
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
            Predicate::Class(_, ty, params, _) => {
                ty.apply_subst(subst);
                params.apply_subst(subst);
            }
            Predicate::HasField(ty, _, field, _) => {
                ty.apply_subst(subst);
                field.apply_subst(subst);
            }
            Predicate::Recv(_, recv_ty, self_ty, _) => {
                recv_ty.apply_subst(subst);
                self_ty.apply_subst(subst);
            }
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        match self {
            Predicate::Class(_, ty, params, _) => {
                ty.apply_subst_all(subst);
                params.apply_subst_all(subst);
            }
            Predicate::HasField(ty, _, field, _) => {
                ty.apply_subst_all(subst);
                field.apply_subst_all(subst);
            }
            Predicate::Recv(_, recv_ty, self_ty, _) => {
                recv_ty.apply_subst_all(subst);
                self_ty.apply_subst_all(subst);
            }
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match self {
            Predicate::Class(_, ty, params, _) => ty
                .free_vars()
                .into_iter()
                .chain(params.free_vars())
                .collect(),
            Predicate::HasField(ty, _, field, _) => ty
                .free_vars()
                .into_iter()
                .chain(field.free_vars())
                .collect(),
            Predicate::Recv(_, recv_ty, self_ty, _) => recv_ty
                .free_vars()
                .into_iter()
                .chain(self_ty.free_vars())
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
            || match class_env.by_instance(&predicate.freeze_vars(), synonyms) {
                Some(candidates) => candidates
                    .iter()
                    .any(|(_, qs)| qs.iter().all(|q| self.entails(q, synonyms, class_env))),
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
    fn match_has_field(
        lhs_record: &T,
        lhs_field: &str,
        lhs_field_ty: &T,
        rhs_record: &T,
        rhs_field: &str,
        rhs_field_ty: &T,
        synonyms: &OrderedTypeSynonyms<T, V>,
    ) -> Option<Subst<V, T>> {
        // Field names must match exactly.
        if lhs_field != rhs_field {
            return None;
        }

        log::debug!(
            "[match_has_field] lhs=({}, {}), rhs=({}, {}), field={}",
            lhs_record,
            lhs_field_ty,
            rhs_record,
            rhs_field_ty,
            lhs_field
        );

        // Try direct match first: HasField(R, f, U) =~ HasField(R', f, U')
        if let Ok((_, subst)) = mgu_ref_slices(
            &[lhs_record, lhs_field_ty],
            &[rhs_record, rhs_field_ty],
            &Subst::new(),
            synonyms,
        ) {
            return Some(Predicate::normalize_instance_subst(subst));
        }

        // Then try a single level of auto-deref on safe pointers:
        // HasField(*R, f, U) =~ HasField(R, f, U')
        if let Some(inner) = lhs_record.maybe_ptr() {
            if let Ok((_, subst)) = mgu_ref_slices(
                &[inner, lhs_field_ty],
                &[rhs_record, rhs_field_ty],
                &Subst::new(),
                synonyms,
            ) {
                return Some(Predicate::normalize_instance_subst(subst));
            }
        }

        None
    }

    /// Normalize a substitution produced while matching a predicate against an
    /// instance head. We may get bindings like:
    ///
    ///   ?t_meta ↦ 'a
    ///   ?t_field ↦ rawptr['a]
    ///
    /// We don't want schema variables like `'a` to appear in solver-space
    /// types. Instead we rewrite every `'a` in RHS types to the corresponding
    /// meta variable (e.g. `?t_meta`) and drop the meta→schema binding,
    /// yielding:
    ///
    ///   ?t_field ↦ rawptr[?t_meta]
    fn normalize_instance_subst(subst: Subst<V, T>) -> Subst<V, T> {
        // Collect mapping from schematic vars to the metas they were unified with.
        let mut schema_to_meta = HashMap::new();
        for (var, ty) in subst.iter() {
            // We only care about bindings from meta variables.
            if !var.is_meta() {
                continue;
            }

            if let Some(schema_var) = ty.maybe_var() {
                // schema_var is a schematic type variable (not a meta).
                if !schema_var.is_meta() {
                    schema_to_meta
                        .entry(schema_var.clone())
                        .or_insert_with(|| var.clone());
                }
            }
        }

        if schema_to_meta.is_empty() {
            return subst;
        }

        // Build a substitution that replaces each schema var with its meta var.
        let mut schema_subst = Subst::new();
        for (schema, meta) in schema_to_meta.iter() {
            schema_subst.insert(schema.clone(), T::var(meta.clone()));
        }

        // Rewrite RHS types and drop trivial self-bindings (v ↦ v).
        let mut result = Subst::new();
        for (var, mut ty) in subst.into_iter() {
            ty.apply_subst(&schema_subst);

            if let Some(v) = ty.maybe_var() {
                if *v == var {
                    continue;
                }
            }

            result.insert(var, ty);
        }

        result
    }

    pub fn class(name: String, ty: T, params: Vec<T>) -> Self {
        Predicate::Class(name, ty, params, PhantomData)
    }

    pub fn has_field(ty: T, name: String, field: T) -> Self {
        Predicate::HasField(ty, name, field, PhantomData)
    }

    pub fn recv(kind: RecvKind, recv_ty: T, self_ty: T) -> Self {
        Predicate::Recv(kind, recv_ty, self_ty, PhantomData)
    }

    pub fn is_record_qualifier(&self) -> bool {
        matches!(self, Predicate::HasField(..))
    }

    pub fn in_head_normal_form(&self) -> bool {
        match self {
            Predicate::Class(_, ty, _, _) => ty.in_head_normal_form(),
            Predicate::HasField(ty, _, field_ty, _) => {
                ty.in_head_normal_form() || field_ty.in_head_normal_form()
            }
            Predicate::Recv(_, _, _, _) => false,
        }
    }

    pub fn freeze_vars(&self) -> Self {
        match self {
            Predicate::Class(name, ty, params, ph) => Predicate::Class(
                name.clone(),
                ty.freeze_vars(),
                params.iter().map(T::freeze_vars).collect(),
                ph.clone(),
            ),
            Predicate::HasField(ty, field_name, field_ty, ph) => Predicate::HasField(
                ty.freeze_vars(),
                field_name.clone(),
                field_ty.freeze_vars(),
                ph.clone(),
            ),
            Predicate::Recv(recv_kind, recv_ty, self_ty, ph) => Predicate::Recv(
                recv_kind.clone(),
                recv_ty.freeze_vars(),
                self_ty.freeze_vars(),
                ph.clone(),
            ),
        }
    }

    pub fn unfreeze_vars(&self) -> Self
    where
        V: FromStr,
        <V as FromStr>::Err: std::fmt::Debug,
    {
        match self {
            Predicate::Class(name, ty, params, ph) => Predicate::Class(
                name.clone(),
                ty.unfreeze_vars(),
                params.iter().map(T::unfreeze_vars).collect(),
                ph.clone(),
            ),
            Predicate::HasField(ty, field_name, field_ty, ph) => Predicate::HasField(
                ty.unfreeze_vars(),
                field_name.clone(),
                field_ty.unfreeze_vars(),
                ph.clone(),
            ),
            Predicate::Recv(recv_kind, recv_ty, self_ty, ph) => Predicate::Recv(
                recv_kind.clone(),
                recv_ty.unfreeze_vars(),
                self_ty.unfreeze_vars(),
                ph.clone(),
            ),
        }
    }

    pub fn flatten(&self) -> Vec<&T> {
        todo!()
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
            (
                Predicate::Class(name1, lhs, lhs_params, _),
                Predicate::Class(name2, rhs, rhs_params, _),
            ) if name1 == name2 => {
                let lhs_all = std::iter::once(lhs)
                    .chain(lhs_params.iter())
                    .collect::<Vec<_>>();
                let rhs_all = std::iter::once(rhs)
                    .chain(rhs_params.iter())
                    .collect::<Vec<_>>();
                match mgu_ref_slices(&lhs_all, &rhs_all, &Subst::new(), synonyms) {
                    Ok((_, mut subst)) => {
                        for (_, ty) in subst.iter_mut() {
                            *ty = ty.unfreeze_vars();
                        }
                        Some(Self::normalize_instance_subst(subst))
                    }
                    Err(_) => None,
                }
            }
            (
                Predicate::HasField(lhs_ty, lhs_field, lhs_field_ty, _),
                Predicate::HasField(rhs_ty, rhs_field, rhs_field_ty, _),
            ) => Predicate::match_has_field(
                lhs_ty,
                lhs_field,
                lhs_field_ty,
                rhs_ty,
                rhs_field,
                rhs_field_ty,
                synonyms,
            ),
            (
                Predicate::Recv(kind1, lhs_recv, lhs_self, _),
                Predicate::Recv(kind2, rhs_recv, rhs_self, _),
            ) if kind1 == kind2 => {
                match mgu_ref_slices(
                    &[lhs_recv, lhs_self],
                    &[rhs_recv, rhs_self],
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
