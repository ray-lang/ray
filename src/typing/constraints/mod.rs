mod satisfiable;
pub mod tree;

use rand::Rng;
pub use satisfiable::*;

use std::{
    collections::{HashMap, HashSet, VecDeque},
    iter::FromIterator,
};

use itertools::Itertools;

use crate::{
    convert::ToSet,
    span::Source,
    typing::{
        predicate::TyPredicate,
        ty::{Ty, TyVar},
        ApplySubst, Subst,
    },
    utils::{join, map_join},
};

use super::{
    assumptions::AssumptionSet,
    state::TyEnv,
    traits::{CollectTyVars, HasFreeVars, PolymorphismInfo, QualifyTypes, QuantifyTypes},
    ApplySubstMut,
};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EqConstraint(Ty, Ty);

impl Into<ConstraintKind> for EqConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Eq(self)
    }
}

impl std::fmt::Debug for EqConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ≡ {}", self.0, self.1)
    }
}

impl EqConstraint {
    pub fn new(t: Ty, u: Ty) -> Constraint {
        Constraint::new(EqConstraint(t, u))
    }

    pub fn lift(aset: &AssumptionSet, env: &TyEnv) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, lhs_ty) in env.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(tys) = aset.get(x) {
                for rhs_ty in tys.iter().sorted() {
                    cl.push((
                        rhs_ty.to_string(),
                        EqConstraint::new(lhs_ty.clone(), rhs_ty.clone()),
                    ));
                }
            }
        }

        cl
    }

    pub fn unpack(self) -> (Ty, Ty) {
        (self.0, self.1)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct VarConstraint(TyVar, Ty);

impl Into<ConstraintKind> for VarConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Var(self)
    }
}

impl std::fmt::Debug for VarConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ⤇ {}", self.0, self.1)
    }
}

impl VarConstraint {
    pub fn new(v: TyVar, ty: Ty) -> Constraint {
        Constraint::new(VarConstraint(v, ty))
    }

    pub fn unpack(self) -> (TyVar, Ty) {
        (self.0, self.1)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GenConstraint(Vec<Ty>, TyVar, Ty);

impl Into<ConstraintKind> for GenConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Gen(self)
    }
}

impl std::fmt::Debug for GenConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} := Gen([{}], {})",
            self.1,
            join(&self.0, ", "),
            self.2
        )
    }
}

impl GenConstraint {
    pub fn new(v: Vec<Ty>, tv: TyVar, t: Ty) -> Constraint {
        Constraint::new(GenConstraint(v, tv, t))
    }

    pub fn unpack(self) -> (Vec<Ty>, TyVar, Ty) {
        (self.0, self.1, self.2)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct InstConstraint(Ty, Ty);

impl Into<ConstraintKind> for InstConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Inst(self)
    }
}

impl std::fmt::Debug for InstConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ≼ {}", self.0, self.1)
    }
}

impl InstConstraint {
    pub fn new(t: Ty, u: Ty) -> Constraint {
        Constraint::new(InstConstraint(t, u))
    }

    pub fn unpack(self) -> (Ty, Ty) {
        (self.0, self.1)
    }

    pub fn lift(aset: &AssumptionSet, sigs: &TyEnv) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, tys) in aset.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(rhs_ty) = sigs.get(x) {
                for lhs_ty in tys {
                    cl.push((
                        lhs_ty.to_string(),
                        InstConstraint::new(lhs_ty.clone(), rhs_ty.clone()),
                    ));
                }
            }
        }

        cl
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SkolConstraint(Vec<TyVar>, Ty, Ty);

impl Into<ConstraintKind> for SkolConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Skol(self)
    }
}

impl std::fmt::Debug for SkolConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} ≽{} {}",
            self.1,
            if self.0.len() == 0 {
                str!("∅")
            } else {
                format!("{:?}", self.0)
            },
            self.2
        )
    }
}

impl SkolConstraint {
    pub fn new<I: IntoIterator<Item = TyVar>>(v: I, t: Ty, u: Ty) -> Constraint {
        Constraint::new(SkolConstraint(Vec::from_iter(v), t, u))
    }

    pub fn lift(env: &TyEnv, sigs: &TyEnv, mono_tys: &HashSet<TyVar>) -> Vec<(String, Constraint)> {
        let mut cl = vec![];
        for (x, lhs_ty) in env.iter().sorted_by_key(|&(x, _)| x) {
            if let Some(rhs_ty) = sigs.get(x) {
                cl.push((
                    lhs_ty.to_string(),
                    Constraint::new(SkolConstraint(
                        mono_tys.iter().cloned().collect(),
                        lhs_ty.clone(),
                        rhs_ty.clone(),
                    )),
                ));
            }
        }

        cl
    }

    pub fn unpack(self) -> (Vec<TyVar>, Ty, Ty) {
        (self.0, self.1, self.2)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ImplicitConstraint(Vec<TyVar>, Ty, Ty);

impl Into<ConstraintKind> for ImplicitConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Implicit(self)
    }
}

impl std::fmt::Debug for ImplicitConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} ≤{} {}",
            self.1,
            if self.0.len() == 0 {
                str!("∅")
            } else {
                format!("{:?}", self.0)
            },
            self.2
        )
    }
}

impl ImplicitConstraint {
    pub fn new(vs: Vec<TyVar>, t: Ty, u: Ty) -> Constraint {
        Constraint::new(ImplicitConstraint(vs, t, u))
    }

    pub fn unpack(self) -> (Vec<TyVar>, Ty, Ty) {
        (self.0, self.1, self.2)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProveConstraint(TyPredicate);

impl Into<ConstraintKind> for ProveConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Prove(self)
    }
}

impl std::fmt::Debug for ProveConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Prove ({})", self.0)
    }
}

impl ProveConstraint {
    pub fn new(q: TyPredicate) -> Constraint {
        Constraint::new(ProveConstraint(q))
    }

    pub fn get_predicate(self) -> TyPredicate {
        self.0
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AssumeConstraint(TyPredicate);

impl Into<ConstraintKind> for AssumeConstraint {
    fn into(self) -> ConstraintKind {
        ConstraintKind::Assume(self)
    }
}

impl std::fmt::Debug for AssumeConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Assume ({})", self.0)
    }
}

impl AssumeConstraint {
    pub fn new(q: TyPredicate) -> Constraint {
        Constraint::new(AssumeConstraint(q))
    }

    pub fn get_predicate(self) -> TyPredicate {
        self.0
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ConstraintKind {
    Eq(EqConstraint),
    Var(VarConstraint),
    Gen(GenConstraint),
    Inst(InstConstraint),
    Skol(SkolConstraint),
    Implicit(ImplicitConstraint),
    Prove(ProveConstraint),
    Assume(AssumeConstraint),
}

impl std::fmt::Debug for ConstraintKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintKind::Eq(c) => write!(f, "{:?}", c),
            ConstraintKind::Var(c) => write!(f, "{:?}", c),
            ConstraintKind::Gen(c) => write!(f, "{:?}", c),
            ConstraintKind::Inst(c) => write!(f, "{:?}", c),
            ConstraintKind::Skol(c) => write!(f, "{:?}", c),
            ConstraintKind::Implicit(c) => write!(f, "{:?}", c),
            ConstraintKind::Prove(c) => write!(f, "{:?}", c),
            ConstraintKind::Assume(c) => write!(f, "{:?}", c),
        }
    }
}

impl QualifyTypes for ConstraintKind {
    fn qualify_tys(&mut self, _: &Vec<TyPredicate>) {
        todo!()
    }
}

impl ConstraintKind {
    fn get_tys_mut(&mut self) -> std::vec::IntoIter<&mut Ty> {
        let v = match self {
            ConstraintKind::Eq(EqConstraint(s, t))
            | ConstraintKind::Inst(InstConstraint(s, t))
            | ConstraintKind::Implicit(ImplicitConstraint(_, s, t))
            | ConstraintKind::Skol(SkolConstraint(_, s, t)) => vec![s, t],
            ConstraintKind::Gen(GenConstraint(m, _, t)) => {
                m.iter_mut().chain(std::iter::once(t)).collect()
            }
            ConstraintKind::Var(VarConstraint(_, ty)) => vec![ty],
            ConstraintKind::Prove(ProveConstraint(_))
            | ConstraintKind::Assume(AssumeConstraint(_)) => vec![],
        };
        v.into_iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstraintInfo {
    pub src: Vec<Source>,
}

impl PolymorphismInfo for ConstraintInfo {
    fn inst_ty(self, _: &Ty) -> Self
    where
        Self: Sized,
    {
        self
    }

    fn skol_ty(self, _: &Ty) -> Self
    where
        Self: Sized,
    {
        self
    }
}

impl ConstraintInfo {
    pub fn new() -> ConstraintInfo {
        ConstraintInfo { src: vec![] }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Constraint {
    pub id: u64,
    pub kind: ConstraintKind,
    pub info: ConstraintInfo,
}

impl std::hash::Hash for Constraint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl std::fmt::Debug for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} (src=[{}])",
            self.kind,
            map_join(&self.info.src, ", ", |src| {
                if let Some(span) = src.span {
                    format!("{}:{}", src.filepath, span)
                } else {
                    src.filepath.to_string()
                }
            })
        )
    }
}

impl HasFreeVars for Constraint {
    fn free_vars(&self) -> HashSet<&TyVar> {
        match &self.kind {
            ConstraintKind::Eq(EqConstraint(s, t)) | ConstraintKind::Inst(InstConstraint(s, t)) => {
                s.free_vars().union(&t.free_vars()).map(|&v| v).collect()
            }
            ConstraintKind::Var(VarConstraint(v, t)) => {
                let mut h = HashSet::new();
                h.insert(v);
                h.extend(t.free_vars());
                h
            }
            ConstraintKind::Gen(GenConstraint(m, s, t)) => {
                let mut h = HashSet::new();
                h.insert(s);
                h.extend(m.free_vars());
                h.extend(t.free_vars());
                h
            }
            ConstraintKind::Skol(SkolConstraint(vs, s, t))
            | ConstraintKind::Implicit(ImplicitConstraint(vs, s, t)) => {
                let mut h = HashSet::new();
                h.extend(vs.iter());
                h.extend(s.free_vars());
                h.extend(t.free_vars());
                h
            }
            ConstraintKind::Prove(_) | ConstraintKind::Assume(_) => HashSet::new(),
        }
    }
}

impl ApplySubst for Constraint {
    fn apply_subst(self, subst: &Subst) -> Self {
        let info = self.info;
        let kind = match self.kind {
            ConstraintKind::Eq(EqConstraint(s, t)) => {
                EqConstraint(s.apply_subst(subst), t.apply_subst(subst)).into()
            }
            ConstraintKind::Var(VarConstraint(v, t)) => {
                VarConstraint(v.apply_subst(subst), t.apply_subst(subst)).into()
            }
            ConstraintKind::Inst(InstConstraint(s, t)) => {
                InstConstraint(s.apply_subst(subst), t.apply_subst(subst)).into()
            }
            ConstraintKind::Gen(GenConstraint(m, s, t)) => {
                GenConstraint(m.apply_subst(subst), s, t.apply_subst(subst)).into()
            }
            ConstraintKind::Skol(SkolConstraint(vs, s, t)) => SkolConstraint(
                vs.apply_subst(subst),
                s.apply_subst(subst),
                t.apply_subst(subst),
            )
            .into(),
            ConstraintKind::Implicit(ImplicitConstraint(vs, s, t)) => ImplicitConstraint(
                vs.apply_subst(subst),
                s.apply_subst(subst),
                t.apply_subst(subst),
            )
            .into(),
            ConstraintKind::Prove(ProveConstraint(p)) => {
                ProveConstraint(p.apply_subst(subst)).into()
            }
            ConstraintKind::Assume(AssumeConstraint(p)) => {
                AssumeConstraint(p.apply_subst(subst)).into()
            }
        };

        let mut rng = rand::thread_rng();
        let id = rng.gen::<u64>();
        Constraint { id, kind, info }
    }
}

impl QualifyTypes for Constraint {
    fn qualify_tys(&mut self, preds: &Vec<TyPredicate>) {
        self.kind.get_tys_mut().qualify_tys(preds);
    }
}

// impl QualifyTypes for Vec<Constraint> {
//     fn qualify_tys(&mut self, preds: &Vec<TyPredicate>) {
//         todo!()
//     }
// }

impl QuantifyTypes for Constraint {
    fn quantify_tys(&mut self) {
        self.kind.get_tys_mut().quantify_tys();
    }
}

impl CollectTyVars for Constraint {
    fn collect_tyvars(&self) -> Vec<TyVar> {
        match &self.kind {
            ConstraintKind::Eq(EqConstraint(s, t)) | ConstraintKind::Inst(InstConstraint(s, t)) => {
                let mut vars = s.collect_tyvars();
                vars.extend(t.collect_tyvars());
                vars
            }
            ConstraintKind::Var(VarConstraint(v, t)) => {
                let mut vars = vec![v.clone()];
                vars.extend(t.collect_tyvars());
                vars
            }
            ConstraintKind::Gen(GenConstraint(m, s, t)) => {
                let mut vars = vec![];
                vars.push(s.clone());
                vars.extend(m.collect_tyvars());
                vars.extend(t.collect_tyvars());
                vars
            }
            ConstraintKind::Skol(SkolConstraint(vs, s, t))
            | ConstraintKind::Implicit(ImplicitConstraint(vs, s, t)) => {
                let mut vars = vec![];
                vars.extend(vs.clone());
                vars.extend(s.collect_tyvars());
                vars.extend(t.collect_tyvars());
                vars
            }
            ConstraintKind::Prove(ProveConstraint(p))
            | ConstraintKind::Assume(AssumeConstraint(p)) => p.collect_tyvars(),
        }
    }
}

impl Constraint {
    pub fn new<T: Into<ConstraintKind>>(c: T) -> Constraint {
        let mut rng = rand::thread_rng();
        let id = rng.gen::<u64>();
        Constraint {
            id,
            kind: c.into(),
            info: ConstraintInfo::new(),
        }
    }

    pub fn with_src(mut self, src: Source) -> Constraint {
        self.info.src.push(src);
        self
    }

    pub fn with_info(mut self, info: ConstraintInfo) -> Constraint {
        self.info = info;
        self
    }
}

#[derive(Default)]
pub struct ConstraintList {
    index: HashMap<u64, Constraint>,
    var_map: HashMap<TyVar, HashSet<u64>>,
    reverse_map: HashMap<u64, HashSet<TyVar>>,
    constraints: VecDeque<u64>,
}

impl std::fmt::Debug for ConstraintList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cs = self.constraints.clone();
        f.debug_list()
            .entries(cs.into_iter().map(|c| self.index.get(&c).unwrap()))
            .finish()
    }
}

impl Extend<ConstraintList> for ConstraintList {
    fn extend<T: IntoIterator<Item = ConstraintList>>(&mut self, iter: T) {
        for l in iter {
            self.extend(l);
        }
    }
}

impl Extend<Constraint> for ConstraintList {
    fn extend<T: IntoIterator<Item = Constraint>>(&mut self, iter: T) {
        for c in iter {
            self.push(c);
        }
    }
}

impl IntoIterator for ConstraintList {
    type Item = Constraint;
    type IntoIter = std::vec::IntoIter<Constraint>;

    fn into_iter(mut self) -> Self::IntoIter {
        // clear to remove the refs so that they can be unwrapped
        self.var_map.clear();
        self.reverse_map.clear();
        self.to_vec().into_iter()
    }
}

impl Into<ConstraintList> for Vec<Constraint> {
    fn into(self) -> ConstraintList {
        let mut cl = ConstraintList::new();
        cl.extend(self);
        cl
    }
}

impl ApplySubst for ConstraintList {
    fn apply_subst(self, subst: &Subst) -> Self {
        let mut cl = self;
        let mut reindex = HashSet::new();
        for v in subst.keys() {
            if let Some(cs) = cl.var_map.get(v) {
                for id in cs {
                    if let Some(c) = cl.index.get_mut(id) {
                        c.apply_subst_mut(subst);
                        reindex.insert(*id);
                    }
                }
            }
        }

        for id in reindex {
            cl.index_constraint(id);
        }
        cl
    }
}

impl ConstraintList {
    pub fn new() -> ConstraintList {
        ConstraintList {
            index: HashMap::new(),
            var_map: HashMap::new(),
            reverse_map: HashMap::new(),
            constraints: VecDeque::new(),
        }
    }

    pub fn to_vec(mut self) -> Vec<Constraint> {
        let mut v = vec![];
        for c in self.constraints {
            v.push(self.index.remove(&c).unwrap());
        }
        v
    }

    pub fn simplify(&mut self) {
        enum Side {
            Left,
            Right,
        }

        fn cs_match(lhs: &Constraint, rhs: &Constraint) -> Option<Side> {
            match (&lhs.kind, &rhs.kind) {
                (
                    ConstraintKind::Eq(EqConstraint(lhs_a, lhs_b)),
                    ConstraintKind::Eq(EqConstraint(rhs_a, rhs_b)),
                ) => {
                    if matches!((lhs_a, rhs_a), (Ty::Var(lhs_tv), Ty::Var(rhs_tv)) if lhs_tv == rhs_tv)
                    {
                        Some(Side::Left)
                    } else if matches!((lhs_b, rhs_b), (Ty::Var(lhs_tv), Ty::Var(rhs_tv)) if lhs_tv == rhs_tv)
                    {
                        Some(Side::Right)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }

        let mut i = 0;
        while i < self.constraints.len() {
            let lhs_id = self.constraints[i];
            if !matches!(
                &self.index.get(&lhs_id).unwrap().kind,
                ConstraintKind::Eq(_)
            ) {
                i += 1;
                continue;
            }

            let mut lhs_cs = vec![];
            let mut rhs_cs = vec![];
            let mut j = i + 1;
            while j < self.constraints.len() {
                let rhs_id = self.constraints[j];
                if !matches!(
                    &self.index.get(&rhs_id).unwrap().kind,
                    ConstraintKind::Eq(_)
                ) {
                    j += 1;
                    continue;
                }

                if let Some(side) = cs_match(
                    &self.index.get(&lhs_id).unwrap(),
                    &self.index.get(&rhs_id).unwrap(),
                ) {
                    let eq = variant!(self.remove(j).kind, if ConstraintKind::Eq(e));
                    match side {
                        Side::Left => lhs_cs.push(eq),
                        Side::Right => rhs_cs.push(eq),
                    }
                }

                j += 1;
            }

            if lhs_cs.len() != 0 {
                let EqConstraint(_, t) = variant!(&mut self.index.get_mut(&lhs_id).unwrap().kind, if ConstraintKind::Eq(eq));
                for c in lhs_cs {
                    let (_, u) = c.unpack();
                    t.union(u);
                }
                log::debug!("union ty: {}", t);
            }

            if rhs_cs.len() != 0 {
                let EqConstraint(t, _) = variant!(&mut self.index.get_mut(&lhs_id).unwrap().kind, if ConstraintKind::Eq(eq));
                for c in rhs_cs {
                    let (u, _) = c.unpack();
                    t.union(u);
                }
                log::debug!("union ty: {}", t);
            }

            i += 1;
        }
    }

    fn index_constraint(&mut self, id: u64) {
        let c = self.index.get(&id).unwrap();
        let tyvars = c.collect_tyvars();
        for v in tyvars.iter() {
            if let Some(cs) = self.var_map.get_mut(v) {
                cs.insert(id);
            } else {
                let mut set = HashSet::new();
                set.insert(id);
                self.var_map.insert(v.clone(), set);
            }
        }

        self.reverse_map.insert(id, tyvars.to_set());
    }

    fn remove(&mut self, idx: usize) -> Constraint {
        let id = self.constraints.remove(idx).unwrap();
        for v in self.reverse_map.remove(&id).unwrap() {
            if let Some(cs) = self.var_map.get_mut(&v) {
                cs.remove(&id);
            }
        }
        self.index.remove(&id).unwrap()
    }

    pub fn push(&mut self, c: Constraint) {
        let id = c.id;
        self.index.insert(id, c);
        self.index_constraint(id);
        self.constraints.push_back(id);
    }

    pub fn push_front(&mut self, c: Constraint) {
        let id = c.id;
        self.index.insert(id, c);
        self.index_constraint(id);
        self.constraints.push_front(id);
    }

    pub fn pop_front(&mut self) -> Option<Constraint> {
        match self.constraints.pop_front() {
            Some(id) => {
                for v in self.reverse_map.remove(&id).unwrap() {
                    if let Some(cs) = self.var_map.get_mut(&v) {
                        cs.remove(&id);
                    }
                }
                Some(self.index.remove(&id).unwrap())
            }
            _ => None,
        }
    }
}
