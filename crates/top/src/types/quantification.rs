use std::collections::HashMap;

use crate::util::DisplayableVec;

use super::{Qualification, Subst, Substitutable, Ty};

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
    Self: std::fmt::Display,
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

pub trait HasSkolems {
    fn all_skolems(&self) -> Vec<u32>;
    fn change_skolems(&mut self, map: &HashMap<u32, Ty>);

    fn bind_skolems(mut self, skolems: &[u32]) -> ForAll<Self>
    where
        Self: Sized,
    {
        let skolems = skolems
            .iter()
            .copied()
            .chain(self.all_skolems().into_iter())
            .map(|i| (i, Ty::Var(i)))
            .collect::<HashMap<_, _>>();
        let vars = skolems.keys().copied().collect();
        self.change_skolems(&skolems);
        ForAll {
            vars,
            quantor_map: HashMap::new(),
            ty: self,
        }
    }

    fn unskolemize(self, skolems: &[u32]) -> ForAll<Self>
    where
        Self: Sized,
    {
        self.bind_skolems(skolems)
    }
}

impl<T> HasSkolems for Vec<T>
where
    T: HasSkolems,
{
    fn all_skolems(&self) -> Vec<u32> {
        self.iter().flat_map(|ty| ty.all_skolems()).collect()
    }

    fn change_skolems(&mut self, map: &HashMap<u32, Ty>) {
        for ty in self.iter_mut() {
            ty.change_skolems(map);
        }
    }
}

impl HasSkolems for Ty {
    fn all_skolems(&self) -> Vec<u32> {
        match self {
            Ty::Var(_) => vec![],
            Ty::Const(name) => {
                if name.starts_with("#") {
                    let id = name[1..].parse::<u32>().unwrap();
                    vec![id]
                } else {
                    vec![]
                }
            }
            Ty::Tuple(tys) => tys.iter().flat_map(|ty| ty.all_skolems()).collect(),
            Ty::App(lhs, rhs) => {
                let mut skolems = lhs.all_skolems();
                skolems.extend(rhs.all_skolems());
                skolems
            }
        }
    }

    fn change_skolems(&mut self, map: &HashMap<u32, Ty>) {
        match self {
            Ty::Var(_) => (),
            Ty::Const(name) => {
                if name.starts_with("#") {
                    let id = name[1..].parse::<u32>().unwrap();
                    if let Some(ty) = map.get(&id) {
                        *self = ty.clone();
                    }
                }
            }
            Ty::Tuple(tys) => tys.change_skolems(map),
            Ty::App(lhs, rhs) => {
                lhs.change_skolems(map);
                rhs.change_skolems(map);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ForAll<T> {
    pub vars: Vec<u32>,
    pub quantor_map: HashMap<u32, String>,
    pub ty: T,
}

impl<T> std::fmt::Display for ForAll<T>
where
    T: Substitutable + ShowQuantors,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.ty
                .show_quantors_without(&ShowQuantorOptions::default())
        )
    }
}

impl<T> ShowQuantors for ForAll<T>
where
    T: Clone + Substitutable + ShowQuantors,
{
    fn show_quantors_without(&self, options: &ShowQuantorOptions) -> String {
        let freevars = self.ty.free_vars();
        let qs = self
            .vars
            .iter()
            .filter(|&id| !freevars.contains(id))
            .collect::<Vec<_>>();

        // find an appropriate name for bound type variables that are in the name map
        let qmap1 = if !options.use_name_map || options.show_all_same {
            HashMap::new()
        } else {
            let (map, _) = self.quantor_map.iter().fold(
                (HashMap::new(), options.dont_use_identifiers.clone()),
                |(mut map, mut dont_use_identifiers), (id, name)| {
                    if qs.contains(&id) {
                        let new_name = (1..)
                            .filter_map(|i| {
                                let n = format!("{}{}", name, i);
                                if !dont_use_identifiers.contains(&n) {
                                    Some(n)
                                } else {
                                    None
                                }
                            })
                            .next()
                            .unwrap();
                        map.insert(*id, new_name.clone());
                        dont_use_identifiers.push(new_name);
                    }

                    (map, dont_use_identifiers)
                },
            );
            map
        };

        let dont_use = qmap1
            .values()
            .chain(options.dont_use_identifiers.iter())
            .collect::<Vec<_>>();

        // find a name for the other bound type variables
        let qmap2 = if options.show_all_same {
            HashMap::new()
        } else {
            qs.iter()
                .filter(|q| !qmap1.contains_key(q))
                .copied()
                .copied()
                .zip(variable_list().filter(|v| !dont_use.contains(&v)))
                .collect()
        };

        let dont_use = qmap2
            .values()
            .chain(dont_use.into_iter())
            .cloned()
            .collect::<Vec<_>>();

        let freevars = self
            .ty
            .free_vars()
            .into_iter()
            .filter(|&id| !qmap1.contains_key(&id) && !qmap2.contains_key(&id))
            .collect::<Vec<_>>();

        let subst = qmap1
            .into_iter()
            .chain(qmap2.into_iter())
            .map(|(i, s)| (i, Ty::Const(s)))
            .chain(
                freevars
                    .into_iter()
                    .map(|i| (i, Ty::Const(format!("{}{}", options.variable_prefix, i)))),
            )
            .collect::<Subst>();

        let quantor_text = if qs.is_empty() || !options.show_toplevel_quantors {
            "".to_string()
        } else {
            let mut quantor_text = "forall ".to_string();
            for (i, var) in qs.into_iter().enumerate() {
                if i > 0 {
                    quantor_text.push_str(", ");
                }

                let mut ty = Ty::Var(*var);
                ty.apply_subst(&subst);

                quantor_text.push_str(&format!("{}", ty));
            }
            quantor_text.push_str(".");
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

impl<T> Substitutable for ForAll<T>
where
    T: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        let mut subst = subst.clone();
        subst.remove_domain(&self.vars);
        self.ty.apply_subst(&subst);
    }

    fn free_vars(&self) -> Vec<u32> {
        self.ty
            .free_vars()
            .into_iter()
            .filter(|var| !self.vars.contains(var))
            .collect()
    }
}

impl<T> ForAll<T> {
    pub fn new(ty: T) -> Self {
        ForAll {
            vars: vec![],
            quantor_map: HashMap::new(),
            ty,
        }
    }

    pub fn quantifiers(&self) -> &Vec<u32> {
        &self.vars
    }

    pub fn unquantified(&self) -> &T {
        &self.ty
    }

    pub fn unquantify(self) -> T {
        self.ty
    }
}

impl<T> ForAll<T>
where
    T: Substitutable + Clone,
{
    pub fn introduce_tyvars(self, i: u32) -> (u32, T) {
        let ForAll { vars, mut ty, .. } = self;
        let subst = vars
            .iter()
            .zip(i..)
            .map(|(&t, u)| (t, Ty::Var(u)))
            .collect::<Subst>();
        ty.apply_subst(&subst);
        (i + vars.len() as u32, ty)
    }

    pub fn introduce_skolems(self, i: u32) -> (u32, T) {
        let ForAll { vars, mut ty, .. } = self;
        let subst = vars
            .iter()
            .cloned()
            .zip((i..).map(|id| Ty::skolem(id)))
            .collect::<Subst>();
        ty.apply_subst(&subst);
        (i + vars.len() as u32, ty)
    }

    pub fn instantiate(&self, n: u32) -> (u32, T) {
        let forall = self.clone();
        forall.introduce_tyvars(n)
    }

    pub fn skolemize(self, i: u32) -> (u32, T) {
        self.introduce_skolems(i)
    }
}

impl<T, U> ForAll<Qualification<Vec<T>, U>>
where
    T: std::fmt::Display + Clone,
    U: std::fmt::Display + Clone,
{
    pub fn displayable(&self) -> ForAll<Qualification<DisplayableVec<T>, U>> {
        let ty = self.ty.clone();
        ForAll {
            vars: self.vars.clone(),
            quantor_map: self.quantor_map.clone(),
            ty: ty.into(),
        }
    }
}

pub struct VariableListIter {
    ch: char,
    i: usize,
}

impl Iterator for VariableListIter {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let mut s = format!("{}", self.ch);
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
