use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    marker::PhantomData,
    str::FromStr,
};

use serde::{Deserialize, Serialize};

use crate::top::TyVar;

use super::{Subst, Substitutable, Ty};

#[derive(Debug, Clone)]
pub struct ShowQuantorOptions {
    pub show_toplevel_quantors: bool,
    pub dont_use_identifiers: Vec<String>,
    pub variable_prefix: &'static str,
    pub show_all_same: bool,
    pub use_name_map: bool,
}

impl Default for ShowQuantorOptions {
    fn default() -> Self {
        Self {
            show_toplevel_quantors: false,
            dont_use_identifiers: vec![],
            variable_prefix: "?",
            show_all_same: false,
            use_name_map: true,
        }
    }
}

pub trait ShowQuantors
where
    Self: Display,
{
    fn show_quantors(&self) -> String {
        let mut options = ShowQuantorOptions::default();
        options.show_toplevel_quantors = true;
        self.show_quantors_without(&options)
    }

    fn show_quantors_without(&self, _: &ShowQuantorOptions) -> String {
        self.to_string()
    }
}

// impl<T> ShowQuantors for Vec<T> where T: ShowQuantors {
//     fn show_quantors_without(&self, _: &ShowQuantorOptions) -> String {
//         self.to_string()
//     }
// }

pub trait HasSkolems<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn all_skolems(&self) -> Vec<V>
    where
        V: FromStr;

    fn change_skolems(&mut self, map: &HashMap<V, T>);

    fn bind_skolems(mut self, skolems: &[V]) -> ForAll<Self, T, V>
    where
        Self: Sized,
        V: FromStr,
    {
        let skolems = skolems
            .iter()
            .cloned()
            .chain(self.all_skolems().into_iter())
            .map(|i| (i.clone(), T::var(i)))
            .collect::<HashMap<_, _>>();
        let mut vars = skolems.keys().cloned().collect::<Vec<_>>();
        vars.sort();
        vars.dedup();
        self.change_skolems(&skolems);
        ForAll {
            vars,
            ty: self,
            _phantom: PhantomData,
        }
    }

    fn unskolemize(self, skolems: &[V]) -> ForAll<Self, T, V>
    where
        Self: Sized,
        V: FromStr,
    {
        self.bind_skolems(skolems)
    }
}

impl<A, T, V> HasSkolems<T, V> for Vec<A>
where
    A: HasSkolems<T, V>,
    T: Ty<V>,
    V: TyVar + FromStr,
{
    fn all_skolems(&self) -> Vec<V> {
        self.iter().flat_map(|ty| ty.all_skolems()).collect()
    }

    fn change_skolems(&mut self, map: &HashMap<V, T>) {
        for ty in self.iter_mut() {
            ty.change_skolems(map);
        }
    }
}

// impl<V> HasSkolems<V> for Ty<V>
// where
//     V: TyVar + FromStr,
//     <V as FromStr>::Err: Debug,
// {
//     fn all_skolems(&self) -> Vec<V>
//     where
//         V: FromStr,
//     {
//         match self {
//             Ty::Var(_) => vec![],
//             Ty::Const(name) => {
//                 if name.starts_with("#") {
//                     let id = name[1..].parse::<V>().unwrap();
//                     vec![id]
//                 } else {
//                     vec![]
//                 }
//             }
//             Ty::Tuple(tys) => tys.iter().flat_map(|ty| ty.all_skolems()).collect(),
//             Ty::App(lhs, rhs) => {
//                 let mut skolems = lhs.all_skolems();
//                 skolems.extend(rhs.all_skolems());
//                 skolems
//             }
//         }
//     }

//     fn change_skolems(&mut self, map: &HashMap<V, Ty<V>>) {
//         match self {
//             Ty::Var(_) => (),
//             Ty::Const(name) => {
//                 if name.starts_with("#") {
//                     let id = name[1..].parse::<u32>().unwrap();
//                     let var = V::from_u32(id);
//                     if let Some(ty) = map.get(&var) {
//                         *self = ty.clone();
//                     }
//                 }
//             }
//             Ty::Tuple(tys) => tys.change_skolems(map),
//             Ty::App(lhs, rhs) => {
//                 lhs.change_skolems(map);
//                 rhs.change_skolems(map);
//             }
//         }
//     }
// }

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForAll<Q, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub vars: Vec<V>,
    pub ty: Q,
    pub(crate) _phantom: PhantomData<T>,
}

impl<Q, T, V> Debug for ForAll<Q, T, V>
where
    Q: Debug,
    T: Debug + Ty<V>,
    V: Debug + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ForAll")
            .field("vars", &self.vars)
            .field("ty", &self.ty)
            .finish()
    }
}

impl<Q, T, V> Display for ForAll<Q, T, V>
where
    Q: Clone + Substitutable<V, T> + ShowQuantors,
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut options = ShowQuantorOptions::default();
        options.show_toplevel_quantors = true;
        write!(f, "{}", self.show_quantors_without(&options))
    }
}

impl<Q, T, V> Default for ForAll<Q, T, V>
where
    Q: Clone + Default,
    T: Default + Ty<V>,
    V: TyVar,
{
    fn default() -> Self {
        Self {
            vars: Default::default(),
            ty: Default::default(),
            _phantom: Default::default(),
        }
    }
}

impl<Q, T, V> ShowQuantors for ForAll<Q, T, V>
where
    Q: Clone + Substitutable<V, T> + ShowQuantors,
    T: Ty<V> + Display,
    V: TyVar + Display,
{
    fn show_quantors_without(&self, options: &ShowQuantorOptions) -> String {
        let freevars = self.ty.free_vars();
        let mut qs = self
            .vars
            .iter()
            .filter(|id| freevars.contains(id))
            .collect::<Vec<_>>();

        qs.sort();
        qs.dedup();

        // find a name for the other bound type variables
        let qmap = if options.show_all_same {
            HashMap::new()
        } else {
            qs.iter()
                .copied()
                .cloned()
                .zip(variable_list().filter(|v| !options.dont_use_identifiers.contains(&v)))
                .collect()
        };

        let dont_use = qmap
            .values()
            .chain(options.dont_use_identifiers.iter())
            .cloned()
            .collect::<Vec<_>>();

        let freevars = self
            .ty
            .free_vars()
            .into_iter()
            .filter(|&id| !qmap.contains_key(&id))
            .collect::<Vec<_>>();

        let subst = qmap
            .into_iter()
            .map(|(i, s)| (i, T::new(&s)))
            .chain(
                freevars
                    .into_iter()
                    .map(|i| (i.clone(), T::new(&format!("{}", i)))),
            )
            .collect::<Subst<V, T>>();

        let quantor_text = if qs.is_empty() || !options.show_toplevel_quantors {
            "".to_string()
        } else {
            let mut quantor_text = "forall[".to_string();
            for (i, var) in qs.into_iter().enumerate() {
                if i > 0 {
                    quantor_text.push_str(", ");
                }

                let mut ty = T::var(var.clone());
                ty.apply_subst(&subst);

                quantor_text.push_str(&format!("{}", ty));
            }
            quantor_text.push_str("]. ");
            quantor_text
        };

        let mut new_options = options.clone();
        new_options.dont_use_identifiers = dont_use;
        new_options.show_toplevel_quantors = true;

        let mut new_ty = self.ty.clone();
        new_ty.apply_subst(&subst);
        format!(
            "{}{}",
            quantor_text,
            new_ty.show_quantors_without(&new_options)
        )
    }
}

impl<Q, T, V> Substitutable<V, T> for ForAll<Q, T, V>
where
    Q: Substitutable<V, T>,
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        let mut subst = subst.clone();
        subst.remove_domain(&self.vars);
        self.ty.apply_subst(&subst);
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        self.vars.iter_mut().for_each(|var| {
            if let Some(new_var) = subst.get(var).and_then(|ty| ty.maybe_var()) {
                *var = new_var.clone();
            }
        });
        self.ty.apply_subst_all(subst);
    }

    fn free_vars(&self) -> Vec<&V> {
        self.ty
            .free_vars()
            .into_iter()
            .filter(|var| !self.vars.contains(var))
            .collect()
    }
}

impl<Q, T, V> ForAll<Q, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new(vars: Vec<V>, ty: Q) -> Self {
        ForAll {
            vars,
            ty,
            _phantom: PhantomData,
        }
    }

    pub fn mono(ty: Q) -> Self {
        ForAll {
            vars: vec![],
            ty,
            _phantom: PhantomData,
        }
    }

    pub fn quantifiers(&self) -> &Vec<V> {
        &self.vars
    }

    pub fn quantifiers_mut(&mut self) -> &mut Vec<V> {
        &mut self.vars
    }

    pub fn unquantified(&self) -> &Q {
        &self.ty
    }

    pub fn unquantified_mut(&mut self) -> &mut Q {
        &mut self.ty
    }

    pub fn unquantify(self) -> Q {
        self.ty
    }

    pub fn generalize_in_place(&mut self)
    where
        Q: Substitutable<V, T>,
    {
        self.ty.free_vars().into_iter().cloned().for_each(|var| {
            self.vars.push(var.clone());
        });
        self.vars.sort();
        self.vars.dedup();
    }
}

impl<Q, T, V> ForAll<Q, T, V>
where
    Q: Substitutable<V, T> + Clone,
    T: Ty<V>,
    V: TyVar,
{
    pub fn introduce_tyvars_with_map(self, i: u32) -> (u32, Q, Vec<(V, V)>) {
        let ForAll { vars, mut ty, .. } = self;
        let mut subst = Subst::new();
        let mut map = Vec::new();
        let mut counter = i;
        for var in vars.iter() {
            let new_var = V::from_u32(counter);
            subst.insert(var.clone(), Ty::var(new_var.clone()));
            map.push((new_var, var.clone()));
            counter += 1;
        }
        ty.apply_subst(&subst);
        (counter, ty, map)
    }

    pub fn introduce_tyvars(self, i: u32) -> (u32, Q) {
        let (new_unique, ty, _) = self.introduce_tyvars_with_map(i);
        (new_unique, ty)
    }

    pub fn introduce_skolems(self, i: u32) -> (u32, Q)
    where
        V: Display,
    {
        let ForAll { vars, mut ty, .. } = self;
        let subst = vars
            .iter()
            .cloned()
            .zip((i..).map(|id| Ty::skolem(V::from_u32(id))))
            .collect::<Subst<V, T>>();
        ty.apply_subst(&subst);
        (i + vars.len() as u32, ty)
    }

    pub fn instantiate(&self, n: u32) -> (u32, Q) {
        let forall = self.clone();
        forall.introduce_tyvars(n)
    }

    pub fn instantiate_with_map(&self, n: u32) -> (u32, Q, Vec<(V, V)>) {
        let forall = self.clone();
        forall.introduce_tyvars_with_map(n)
    }

    pub fn instantiate_with_types(&self, args: &[T]) -> Q {
        assert!(
            args.len() <= self.vars.len(),
            "not enough quantifiers to instantiate with {} args",
            args.len()
        );

        let subst = self
            .vars
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect::<Subst<V, T>>();

        let mut ty = self.ty.clone();
        ty.apply_subst(&subst);
        ty
    }

    pub fn skolemize(self, i: u32) -> (u32, Q)
    where
        V: Display,
    {
        self.introduce_skolems(i)
    }
}

// impl<P, T, U, V> ForAll<Qualification<Vec<P>, U>, T, V>
// where
//     P: Display + Clone,
//     U: Display + Clone,
//     T: Ty<V>,
//     V: TyVar,
// {
//     pub fn displayable(&self) -> ForAll<Qualification<DisplayableVec<P>, U>, T, V> {
//         let ty = self.ty.clone();
//         ForAll {
//             vars: self.vars.clone(),
//             ty: ty.into(),
//             _phantom: PhantomData,
//         }
//     }
// }

pub struct VariableListIter {
    ch: char,
    i: usize,
}

impl Iterator for VariableListIter {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let mut s = format!("'{}", self.ch);
        if self.i != 0 {
            s.push_str(self.i.to_string().as_str());
        }

        if self.ch == 'z' {
            self.i += 1;
            self.ch = 'a';
        } else {
            self.ch = std::char::from_u32(self.ch as u32 + 1).unwrap();
        }

        Some(s)
    }
}

fn variable_list() -> VariableListIter {
    VariableListIter { ch: 'a', i: 0 }
}
