use std::{
    collections::HashMap,
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use super::{mgu_with_synonyms, Predicate, Subst, Substitutable, Ty};

#[derive(Default)]
pub struct TypeSynonyms(HashMap<String, (usize, Box<dyn Fn(Vec<&Ty>) -> &Ty>)>);

impl Debug for TypeSynonyms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeSynonyms(")?;
        for (i, (k, (v, _))) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} = {{ arity = {} }}", k, v)?;
        }

        write!(f, ")")
    }
}

impl Deref for TypeSynonyms {
    type Target = HashMap<String, (usize, Box<dyn Fn(Vec<&Ty>) -> &Ty>)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TypeSynonyms {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl TypeSynonyms {
    pub fn new() -> Self {
        TypeSynonyms(HashMap::new())
    }

    pub fn add(&mut self, name: String, arity: usize, f: impl Fn(Vec<&Ty>) -> &Ty + 'static) {
        self.insert(name, (arity, Box::new(f)));
    }

    pub fn expand_type(&self, ty: &Ty) -> Ty {
        let ty = self.expand_type_constructor(ty);
        let (ty, xs) = ty.left_spine();
        xs.into_iter()
            .cloned()
            .fold(ty.clone(), |ty, x| Ty::App(Box::new(ty), Box::new(x)))
    }

    pub fn expand_type_constructor<'a>(&self, ty: &'a Ty) -> &'a Ty {
        if let Some(ty) = self.expand_tc(ty) {
            self.expand_type_constructor(ty)
        } else {
            ty
        }
    }

    fn expand_tc<'a>(&self, ty: &'a Ty) -> Option<&'a Ty> {
        match ty.left_spine() {
            (Ty::Const(name), args) => {
                if let Some((arity, f)) = self.get(name) {
                    if args.len() == *arity {
                        Some(f(args))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => Some(ty),
        }
    }

    pub fn is_phantom_synonym(&self, name: &str) -> bool {
        match self.get(name) {
            Some((arity, f)) => {
                let is = (0..(*arity as u32)).collect::<Vec<_>>();
                let vars = is.iter().map(|&i| Ty::Var(i)).collect::<Vec<_>>();
                let ty = f(vars.iter().collect());
                let free_vars = ty.free_vars();
                is.iter().any(|i| !free_vars.contains(i))
            }
            None => false,
        }
    }
}

pub type TypeSynonymOrdering = HashMap<String, usize>;

#[derive(Debug, Default)]
pub struct OrderedTypeSynonyms(TypeSynonymOrdering, TypeSynonyms);

impl Deref for OrderedTypeSynonyms {
    type Target = TypeSynonyms;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl DerefMut for OrderedTypeSynonyms {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.1
    }
}

impl Extend<(String, usize, usize, Box<dyn Fn(Vec<&Ty>) -> &Ty>)> for OrderedTypeSynonyms {
    fn extend<T: IntoIterator<Item = (String, usize, usize, Box<dyn Fn(Vec<&Ty>) -> &Ty>)>>(
        &mut self,
        iter: T,
    ) {
        for (name, arity, order, f) in iter {
            self.insert(name, order, arity, f);
        }
    }
}

impl IntoIterator for OrderedTypeSynonyms {
    type Item = (String, usize, usize, Box<dyn Fn(Vec<&Ty>) -> &Ty>);
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(mut self) -> Self::IntoIter {
        self.0
            .into_iter()
            .map(|(name, ord)| {
                let (arity, f) = self.1.remove(&name).unwrap();
                (name, ord, arity, f)
            })
            .collect::<Vec<_>>()
            .into_iter()
    }
}

impl OrderedTypeSynonyms {
    pub fn new() -> Self {
        OrderedTypeSynonyms(HashMap::new(), TypeSynonyms::new())
    }

    pub fn insert(
        &mut self,
        name: String,
        order: usize,
        arity: usize,
        f: Box<dyn Fn(Vec<&Ty>) -> &Ty>,
    ) {
        self.0.insert(name.clone(), order);
        self.1.add(name, arity, f);
    }

    pub fn order(&self, name: &str) -> Option<usize> {
        self.0.get(name).cloned()
    }

    pub fn expand_ordered<'a>(&self, a: &'a Ty, b: &'a Ty) -> Option<(&'a Ty, &'a Ty)> {
        let f = |ty: &Ty| {
            let (ty, _) = ty.left_spine();
            match ty {
                Ty::Const(name) => self.order(name),
                _ => None,
            }
        };

        match (f(a), f(b)) {
            (Some(i), Some(j)) if i > j => self.expand_tc(b).map(|b| (a, b)),
            (Some(_), _) => self.expand_tc(a).map(|a| (a, b)),
            (_, Some(_)) => self.expand_tc(b).map(|b| (a, b)),
            _ => None,
        }
    }

    pub fn match_predicates(&self, p: &Predicate, q: &Predicate) -> Option<Subst> {
        match (&p, q) {
            (
                Predicate {
                    name: p_name,
                    ty: p_ty,
                },
                Predicate {
                    name: q_name,
                    ty: q_ty,
                },
            ) if p_name == q_name => {
                let p_ty = p_ty.freeze_vars();
                match mgu_with_synonyms(&p_ty, q_ty, &Subst::new(), self) {
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
