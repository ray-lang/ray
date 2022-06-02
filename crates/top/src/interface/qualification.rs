use crate::{
    constraint::TypeConstraintInfo,
    directives::TypeClassDirective,
    state::{HasState, SimpleState},
    types::{ClassEnv, OrderedTypeSynonyms, Predicate, Qualification, Scheme, Substitutable, Ty},
};

use super::{basic::HasBasic, subst::HasSubst, type_inference::HasTypeInference};

pub trait HasQual<T> {
    fn prove_qualifier(&mut self, qualifier: Predicate, info: &T);

    fn prove_qualifiers(&mut self, qualifiers: Vec<Predicate>, info: &T) {
        for qualifier in qualifiers {
            self.prove_qualifier(qualifier, info);
        }
    }

    fn assume_qualifier(&mut self, qualifier: Predicate, info: &T);

    fn assume_qualifiers(&mut self, qualifiers: Vec<Predicate>, info: &T) {
        for qualifier in qualifiers {
            self.assume_qualifier(qualifier, info);
        }
    }

    fn change_qualifiers(&mut self, f: impl FnMut(&Self, &mut Predicate) -> ());

    fn all_qualifiers(&self) -> Vec<&Predicate>;

    fn generalize_with_qualifiers(&self, mono_tys: &Vec<Ty>, ty: &Ty) -> Scheme<Vec<Predicate>> {
        let qual_ty = Qualification::new(vec![], ty.clone());
        qual_ty.generalize(mono_tys)
    }

    fn improve_qualifiers(&mut self, normal: bool) -> Vec<(T, Ty, Ty)> {
        if normal {
            self.improve_qualifiers_normal()
        } else {
            self.improve_qualifiers_final()
        }
    }

    fn improve_qualifiers_normal(&mut self) -> Vec<(T, Ty, Ty)> {
        vec![]
    }

    fn improve_qualifiers_final(&mut self) -> Vec<(T, Ty, Ty)> {
        vec![]
    }

    fn simplify_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<T> + HasBasic<T>,
        T: Clone + TypeConstraintInfo<T>;
    fn ambiguous_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<T> + HasBasic<T>,
        T: Clone + std::fmt::Display + TypeConstraintInfo<T>;

    fn class_env(&self) -> &ClassEnv;
    fn class_env_mut(&mut self) -> &mut ClassEnv;

    fn directives(&self) -> &Vec<TypeClassDirective<T>>;
    fn directives_mut(&mut self) -> &mut Vec<TypeClassDirective<T>>;

    fn context_reduction(&mut self)
    where
        Self: Sized + HasSubst<T> + HasBasic<T>,
        T: Clone + TypeConstraintInfo<T>,
    {
        self.make_subst_consistent();
        self.change_qualifiers(|state, qualifier: &mut Predicate| {
            qualifier.apply_subst_from(state)
        });
        self.improve_qualifiers_fix(true);
        self.simplify_qualifiers();
    }

    fn improve_qualifiers_fix(&mut self, normal: bool)
    where
        Self: HasSubst<T>,
    {
        let improvements = self.improve_qualifiers(normal);
        if improvements.is_empty() {
            return;
        }

        for (info, lhs, rhs) in improvements {
            self.unify_terms(&info, &lhs, &rhs);
        }

        self.make_subst_consistent();
        self.improve_qualifiers_fix(normal);
    }

    fn ambiguities(&mut self)
    where
        Self: Sized + HasSubst<T> + HasBasic<T>,
        T: Clone + std::fmt::Display + TypeConstraintInfo<T>,
    {
        self.context_reduction();
        self.improve_qualifiers_fix(true);
        self.ambiguous_qualifiers();
    }

    fn simplify(&mut self, predicates: Vec<(Predicate, T)>) -> Vec<(Predicate, T)>
    where
        Self: Sized + HasSubst<T> + HasTypeInference<T> + HasBasic<T>,
        T: Clone + TypeConstraintInfo<T>,
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
                new_predicates.remove(i);
            } else {
                i += 1;
            }
        }

        self.test_disjoints(&mut new_predicates);
        new_predicates
    }

    fn test_disjoints(&mut self, predicates: &mut Vec<(Predicate, T)>)
    where
        Self: Sized + HasSubst<T> + HasTypeInference<T> + HasBasic<T>,
        T: Clone + TypeConstraintInfo<T>,
    {
        let mut i = 0;
        while i < predicates.len() {
            let mut j = i + 1;
            let mut removed = false;
            while j < predicates.len() {
                let (curr_pred, curr_info) = &predicates[i];
                let (other_pred, other_info) = &predicates[j];
                let maybe_info = self.directives().iter().find_map(|directive| {
                    if let TypeClassDirective::Disjoint(ss, info) = directive {
                        if ss.contains(&curr_pred.name) && ss.contains(&other_pred.name) {
                            Some(info)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });

                if other_pred.ty == curr_pred.ty && maybe_info.is_some() {
                    let mut info = maybe_info.cloned().unwrap();
                    info.disjoint_directive(
                        &curr_pred.name,
                        curr_info,
                        &other_pred.name,
                        other_info,
                    );
                    self.add_labeled_err("disjoint predicates", info);
                    predicates.remove(j);
                    removed = true;
                } else {
                    j += 1;
                }
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
        predicates: Vec<(Predicate, T)>,
        new_predicates: &mut Vec<(Predicate, T)>,
    ) where
        Self: Sized + HasSubst<T> + HasTypeInference<T> + HasBasic<T>,
        T: Clone + TypeConstraintInfo<T>,
    {
        for (p, info) in predicates {
            if p.in_head_normal_form() {
                new_predicates.push((p, info));
                continue;
            }

            let synonyms = self.type_synonyms();
            let class_env = self.class_env();
            match class_env.by_instance(&p, synonyms) {
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
                    match self.directives().iter().find_map(|directive| {
                        if let TypeClassDirective::Never(q, info) = directive {
                            if synonyms.match_predicates(&p, q).is_some() {
                                Some((q, info))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }) {
                        Some((q, i)) => {
                            new_info.never_directive(q, i);
                        }
                        None => match self.directives().iter().find_map(|directive| {
                            if let TypeClassDirective::Close(s, i) = directive {
                                if &p.name == s {
                                    Some(i)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }) {
                            Some(i) => new_info.close_directive(&p.name, i),
                            _ => new_info.unsolved_predicate(&p, &info),
                        },
                    }

                    self.add_labeled_err("unresolved predicate", new_info);
                }
            }
        }
    }
}
