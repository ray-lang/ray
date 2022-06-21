use std::{
    fmt::{Debug, Display},
    str::FromStr,
};

use crate::{
    constraint::TypeConstraintInfo,
    directives::TypeClassDirective,
    types::{ClassEnv, Predicate, Qualification, Scheme, Substitutable, Ty},
    Predicates, TyVar,
};

use super::{basic::HasBasic, subst::HasSubst, type_inference::HasTypeInference};

pub trait HasQual<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn prove_qualifier(&mut self, qualifier: Predicate<T, V>, info: &I);

    fn prove_qualifiers(&mut self, qualifiers: Predicates<T, V>, info: &I) {
        for qualifier in qualifiers {
            self.prove_qualifier(qualifier, info);
        }
    }

    fn assume_qualifier(&mut self, qualifier: Predicate<T, V>, info: &I);

    fn assume_qualifiers(&mut self, qualifiers: Predicates<T, V>, info: &I) {
        for qualifier in qualifiers {
            self.assume_qualifier(qualifier, info);
        }
    }

    fn change_qualifiers(&mut self, f: impl FnMut(&Self, &mut Predicate<T, V>) -> ());

    fn all_qualifiers(&self) -> Vec<&Predicate<T, V>>;

    fn apply_subst_to_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V>,
    {
        self.change_qualifiers(|state, qualifier: &mut Predicate<T, V>| {
            qualifier.apply_subst_from(state)
        });
    }

    fn generalize_with_qualifiers(
        &self,
        mono_tys: &Vec<T>,
        ty: &T,
    ) -> Scheme<Predicates<T, V>, T, V> {
        let qual_ty = Qualification::new(Predicates::new(), ty.clone());
        qual_ty.generalize_in_ctx(mono_tys)
    }

    fn simplify_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Debug + Clone + TypeConstraintInfo<I, T, V>;
    fn default_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V>;
    fn field_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V>;
    fn ambiguous_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        T: Display,
        I: Clone + Display + TypeConstraintInfo<I, T, V>;

    fn class_env(&self) -> &ClassEnv<T, V>;
    fn class_env_mut(&mut self) -> &mut ClassEnv<T, V>;

    fn directives(&self) -> &Vec<TypeClassDirective<I, T, V>>;
    fn directives_mut(&mut self) -> &mut Vec<TypeClassDirective<I, T, V>>;

    fn context_reduction(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Debug + Clone + TypeConstraintInfo<I, T, V>,
    {
        self.make_subst_consistent();
        self.apply_subst_to_qualifiers();
        self.simplify_qualifiers();
    }

    fn defaults(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        T: Display,
        I: Clone + Debug + Display + TypeConstraintInfo<I, T, V>,
    {
        self.context_reduction();
        self.default_qualifiers();
        self.apply_subst_to_qualifiers();
    }

    fn fields(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        T: Display,
        I: Clone + Debug + Display + TypeConstraintInfo<I, T, V>,
    {
        self.context_reduction();
        self.field_qualifiers();
        self.apply_subst_to_qualifiers();
    }

    fn ambiguities(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        T: Display,
        I: Clone + Debug + Display + TypeConstraintInfo<I, T, V>,
    {
        self.context_reduction();
        self.ambiguous_qualifiers();
    }

    fn simplify(&mut self, predicates: Vec<(Predicate<T, V>, I)>) -> Vec<(Predicate<T, V>, I)>
    where
        Self: Sized + HasSubst<I, T, V> + HasTypeInference<I, T, V> + HasBasic<I, T, V>,
        I: Clone + TypeConstraintInfo<I, T, V>,
        V: Display + Eq,
        <V as FromStr>::Err: Debug,
    {
        let mut new_predicates = vec![];
        self.simplify_preds_into(predicates, &mut new_predicates);

        let mut i = 0;
        while i < new_predicates.len() {
            let (predicate, _) = &new_predicates[i];
            let other_predicates = (&new_predicates[..i])
                .iter()
                .chain(&new_predicates[i + 1..])
                .map(|(p, _)| p)
                .collect::<Vec<_>>();
            if self
                .class_env()
                .superclass_entails(&other_predicates, predicate)
            {
                log::debug!("removing predicate: {}", predicate);
                new_predicates.remove(i);
            } else {
                i += 1;
            }
        }

        self.test_disjoints(&mut new_predicates);
        new_predicates
    }

    fn test_disjoints(&mut self, predicates: &mut Vec<(Predicate<T, V>, I)>)
    where
        Self: Sized + HasSubst<I, T, V> + HasTypeInference<I, T, V> + HasBasic<I, T, V>,
        I: Clone + TypeConstraintInfo<I, T, V>,
        V: Eq,
    {
        let mut i = 0;
        while i < predicates.len() {
            let mut j = i + 1;
            let mut removed = false;
            while j < predicates.len() {
                let (curr_pred, curr_info) = &predicates[i];
                let (other_pred, other_info) = &predicates[j];
                if let (
                    Predicate::Class(curr_name, curr_ty, ..),
                    Predicate::Class(other_name, other_ty, ..),
                ) = (curr_pred, other_pred)
                {
                    match self.find_disjoint_directive(curr_name, other_name) {
                        Some(info) if other_ty == curr_ty => {
                            let mut info = info.clone();
                            info.disjoint_directive(&curr_name, curr_info, &other_name, other_info);
                            self.add_labeled_err("disjoint predicates", info);
                            predicates.remove(j);
                            removed = true;
                            continue;
                        }
                        _ => (),
                    }
                }

                j += 1;
            }

            if removed {
                predicates.remove(i);
            } else {
                i += 1;
            }
        }
    }

    fn simplify_preds_into(
        &mut self,
        predicates: Vec<(Predicate<T, V>, I)>,
        new_predicates: &mut Vec<(Predicate<T, V>, I)>,
    ) where
        Self: Sized + HasSubst<I, T, V> + HasTypeInference<I, T, V> + HasBasic<I, T, V>,
        I: Clone + TypeConstraintInfo<I, T, V>,
        V: Display,
        <V as FromStr>::Err: Debug,
    {
        for (predicate, info) in predicates {
            if predicate.in_head_normal_form() {
                new_predicates.push((predicate, info));
                continue;
            }

            let synonyms = self.type_synonyms();
            let class_env = self.class_env();
            match class_env.by_instance(&predicate, synonyms) {
                Some(predicates) => {
                    let predicates = predicates
                        .into_iter()
                        .map(|p| {
                            let mut info = info.clone();
                            info.parent_predicate(&p);
                            (p, info)
                        })
                        .collect();

                    new_predicates.extend(self.simplify(predicates));
                }
                None => {
                    let mut new_info = info.clone();
                    match self.find_never_directive(&predicate) {
                        Some((q, i)) => {
                            new_info.never_directive(q, i);
                        }
                        None => match self.find_close_directive_info(&predicate) {
                            Some((name, info)) => new_info.close_directive(name, info),
                            _ => new_info.unsolved_predicate(&predicate, &info),
                        },
                    }

                    self.add_labeled_err("unresolved predicate", new_info);
                }
            }
        }
    }

    fn find_disjoint_directive<'a>(
        &'a self,
        curr_name: &'a String,
        other_name: &'a String,
    ) -> Option<&'a I>
    where
        Self: Sized + HasSubst<I, T, V> + HasTypeInference<I, T, V> + HasBasic<I, T, V>,
        I: Clone + TypeConstraintInfo<I, T, V>,
        T: 'a,
        V: Eq + 'a,
    {
        self.directives()
            .iter()
            .find_map(|directive| match directive {
                TypeClassDirective::Disjoint(class_names, info)
                    if class_names.contains(curr_name) && class_names.contains(other_name) =>
                {
                    Some(info)
                }
                _ => None,
            })
    }
    fn find_never_directive(&self, predicate: &Predicate<T, V>) -> Option<(&Predicate<T, V>, &I)>
    where
        Self: Sized + HasSubst<I, T, V> + HasTypeInference<I, T, V> + HasBasic<I, T, V>,
        I: Clone + TypeConstraintInfo<I, T, V>,
        V: Display,
        <V as FromStr>::Err: Debug,
    {
        self.directives()
            .iter()
            .find_map(|directive| match directive {
                TypeClassDirective::Never(other_predicate, info)
                    if predicate
                        .match_with(other_predicate, self.type_synonyms())
                        .is_some() =>
                {
                    Some((other_predicate, info))
                }
                _ => None,
            })
    }

    fn find_close_directive_info<'a>(
        &'a self,
        predicate: &'a Predicate<T, V>,
    ) -> Option<(&'a String, &'a I)>
    where
        Self: Sized + HasSubst<I, T, V> + HasTypeInference<I, T, V> + HasBasic<I, T, V>,
        I: Clone + TypeConstraintInfo<I, T, V>,
        V: Display,
        <V as FromStr>::Err: Debug,
    {
        self.directives()
            .iter()
            .find_map(|directive| match (directive, predicate) {
                (TypeClassDirective::Close(close_name, info), Predicate::Class(class_name, ..))
                    if close_name == class_name =>
                {
                    Some((class_name, info))
                }
                _ => None,
            })
    }
}
