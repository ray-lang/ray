use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use top::Substitutable;

use crate::{
    ast::Path,
    convert::ToSet,
    sort::{topological::TopologicalSort, SortByIndexSlice},
    span::Source,
    typing::ty::{SigmaTy, Ty, TyVar},
};

use super::{
    assumptions::AssumptionSet,
    constraints::{
        tree::{ConstraintTree, NodeTree, StrictTree},
        EqConstraint, GenConstraint, InstConstraint, SkolConstraint,
    },
    info::TypeSystemInfo,
    state::{Env, SigmaEnv, TyEnv, TyVarFactory},
    // traits::HasFreeVars,
};

pub struct BindingGroupAnalysis<'a> {
    groups: Vec<BindingGroup>,
    defs: &'a SigmaEnv,
    svar_factory: &'a mut TyVarFactory,
    mono_tys: &'a HashSet<TyVar>,
}

impl<'a> BindingGroupAnalysis<'a> {
    pub fn new(
        groups: Vec<BindingGroup>,
        defs: &'a SigmaEnv,
        svar_factory: &'a mut TyVarFactory,
        mono_tys: &'a HashSet<TyVar>,
    ) -> BindingGroupAnalysis<'a> {
        BindingGroupAnalysis {
            groups,
            defs,
            svar_factory,
            mono_tys,
        }
    }

    fn organize_groups(&mut self) {
        // sort the groups such that binding group A comes before binding group B
        // if some variable is defined in A (under the enviroment in A) and
        // used in B (under the assumption set in B), disregarding types in sigs

        // first, find groups that mutually recursive, and combine them
        let mut i = 0;
        while i < self.groups.len() {
            let mut j = i + 1;
            while j < self.groups.len() {
                let is_mutually_recursive = {
                    let x = &self.groups[i];
                    let y = &self.groups[j];
                    x.is_mutually_recursive(y, self.defs)
                };

                if is_mutually_recursive {
                    // combine x and y
                    let y = self.groups.remove(j);
                    let x = &mut self.groups[i];
                    x.combine(y);
                } else {
                    j += 1;
                }
            }
            i += 1;
        }

        // create a topology of the binding groups
        let sigs = self.defs;
        let mut ts = petgraph::graphmap::DiGraphMap::new();

        // TopologicalSort::<usize>::new();
        for ((i, lhs), (j, rhs)) in self.groups.iter().enumerate().tuple_combinations() {
            let (lhs_sigs, lhs_use, _) = lhs.borrow();
            let (rhs_sigs, rhs_use, _) = rhs.borrow();

            if lhs_sigs
                .keys()
                .any(|p| rhs_use.contains_key(p) && !sigs.contains_key(p))
            {
                // LHS defines variables used in RHS, so RHS depends on LHS
                // ts.add_dependency(i, j);
                log::debug!("{:#?} depends on {:#?}", rhs, lhs);
                ts.add_edge(i, j, ());
            }

            if rhs_sigs
                .keys()
                .any(|p| lhs_use.contains_key(p) && !sigs.contains_key(p))
            {
                // RHS defines variables used in LHS, LHS depends on RHS
                // ts.add_dependency(j, i);
                log::debug!("{:#?} depends on {:#?}", lhs, rhs);
                ts.add_edge(j, i, ());
            }
        }

        log::debug!("graph: {:?}", petgraph::dot::Dot::with_config(&ts, &[]));

        let mut indices = petgraph::algo::toposort(&ts, None).unwrap();
        if indices.len() == 0 {
            return;
        }

        if indices.len() != self.groups.len() {
            // if there are groups that are completely disjoint,
            // meaning they don't show up in the indices list,
            // then we can just add them to the end
            let set = indices.iter().copied().to_set();
            for i in 0..self.groups.len() {
                if !set.contains(&i) {
                    indices.push(i);
                }
            }
        }

        self.groups.sort_by_index_slice(indices);
    }

    pub fn analyze(&mut self) -> (HashSet<TyVar>, AssumptionSet, ConstraintTree) {
        log::debug!("groups: {:#?}", self.groups);
        self.organize_groups();
        log::debug!("groups: {:#?}", self.groups);
        log::debug!("mono_tys: {:?}", self.mono_tys);
        let mut mono_tys = self.mono_tys.clone();
        let mut aset = AssumptionSet::new();
        let mut ctree = ConstraintTree::empty();
        while let Some(g) = self.groups.pop() {
            let (new_m, new_a, new_t) =
                g.combine_with(&mono_tys, aset, ctree, self.defs, self.svar_factory);
            mono_tys = new_m;
            aset = new_a;
            ctree = new_t;
        }

        (mono_tys, aset, ctree)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct BindingGroup {
    env: TyEnv,
    aset: AssumptionSet,
    ctree: ConstraintTree,
    info: TypeSystemInfo,
}

impl std::fmt::Debug for BindingGroup {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BindingGroup")
            .field("env", &self.env)
            .field("aset", &self.aset)
            .finish()
    }
}

impl BindingGroup {
    pub fn new(env: TyEnv, aset: AssumptionSet, ctree: ConstraintTree) -> BindingGroup {
        BindingGroup {
            env,
            aset,
            ctree,
            info: TypeSystemInfo::default(),
        }
    }

    pub fn empty() -> BindingGroup {
        BindingGroup {
            env: TyEnv::new(),
            aset: AssumptionSet::new(),
            ctree: ConstraintTree::empty(),
            info: TypeSystemInfo::default(),
        }
    }

    pub fn with_src(mut self, src: Source) -> BindingGroup {
        self.info.source.push(src);
        self
    }

    pub fn unpack(self) -> (TyEnv, AssumptionSet, ConstraintTree) {
        (self.env, self.aset, self.ctree)
    }

    pub fn env(&self) -> &TyEnv {
        &self.env
    }

    pub fn borrow(&self) -> (&TyEnv, &AssumptionSet, &ConstraintTree) {
        (&self.env, &self.aset, &self.ctree)
    }

    pub fn borrow_mut(&mut self) -> (&mut TyEnv, &mut AssumptionSet, &mut ConstraintTree) {
        (&mut self.env, &mut self.aset, &mut self.ctree)
    }

    pub fn is_mutually_recursive(&self, other: &BindingGroup, sigs: &SigmaEnv) -> bool {
        let (lhs_sigs, lhs_use, _) = self.borrow();
        let (rhs_sigs, rhs_use, _) = other.borrow();

        lhs_sigs
            .keys()
            .any(|p| rhs_use.contains_key(p) && !sigs.contains_key(p))
            && rhs_sigs
                .keys()
                .any(|p| lhs_use.contains_key(p) && !sigs.contains_key(p))
    }

    pub fn combine(&mut self, other: BindingGroup) {
        let rhs_info = other.info.clone();
        let (lhs_sigs, lhs_use, lhs_t) = self.borrow_mut();
        let (rhs_sigs, rhs_use, rhs_t) = other.unpack();

        for (x, t) in rhs_sigs {
            lhs_sigs.insert(x, t);
        }

        for (x, tys) in rhs_use {
            for t in tys {
                lhs_use.add(x.clone(), t);
            }
        }

        if lhs_t.is_empty() && !rhs_t.is_empty() {
            *lhs_t = rhs_t;
        } else if !lhs_t.is_empty() && !rhs_t.is_empty() {
            lhs_t.replace(|t| NodeTree(vec![t, rhs_t]));
        }
        // if both are empty or lhs is not empty and rhs is empty do nothing

        self.info.source.extend(rhs_info.source);
        self.info.source.sort();
        self.info.source.dedup();
    }

    pub fn combine_with(
        self,
        mono_tys: &HashSet<TyVar>,
        rhs_aset: AssumptionSet,
        rhs_tree: ConstraintTree,
        sigs: &SigmaEnv,
        svar_factory: &mut TyVarFactory,
    ) -> (HashSet<TyVar>, AssumptionSet, ConstraintTree) {
        let info = self.info.clone();
        let env = self.env;
        let lhs_aset = self.aset;
        let lhs_tree = self.ctree;

        log::debug!("next env: {:?}", env);
        log::debug!("next aset: {:?}", lhs_aset);
        log::debug!("current aset: {:?}", rhs_aset);

        // Cl1 = A1 ≼ Σ;
        // We create an instantiation constraint for assumptions in A1
        // for which we have a type scheme in Σ.
        let cl1 = InstConstraint::lift(&lhs_aset, sigs)
            .into_iter()
            .map(|(s, mut c)| {
                c.info_mut().extend(info.clone());
                (s, c)
            })
            .collect::<Vec<_>>();

        // Cl2 = E ≽M Σ;
        // A skolemization constraint is created for each variable in E
        // with a type scheme in Σ. This constraint records the set of
        // monomorphic types passed to bga, and it constrains the type
        // of a definition to be more general than its declared type signature.
        let cl2 = SkolConstraint::lift(&env, sigs, mono_tys)
            .into_iter()
            .map(|(s, mut c)| {
                c.info_mut().extend(info.clone());
                (s, c)
            })
            .collect::<Vec<_>>();

        // A1' = A1\dom(Σ); E' = E\dom(Σ)
        let lhs_aset = lhs_aset - sigs.keys();
        let env = env - sigs.keys();

        // Cl3 = A1' ≡ E'
        let cl3 = EqConstraint::lift(&lhs_aset, &env)
            .into_iter()
            .map(|(s, mut c)| {
                c.info_mut().extend(info.clone());
                (s, c)
            })
            .collect::<Vec<_>>();

        // A1'' = A1'\dom(E')
        let lhs_aset = lhs_aset - env.keys();

        // implicits = zip (dom(E')) [σv1,σv2,...] -- fresh type scheme vars
        let implicits = env
            .keys()
            .sorted()
            .map(|x| (x.clone(), svar_factory.next()))
            .collect::<Vec<_>>();

        let mut c4 = vec![];
        for (x, sv) in implicits.iter() {
            if let Some(t) = env.get(x) {
                let mut c = GenConstraint::new(
                    mono_tys.iter().cloned().map(|v| Ty::Var(v)).collect(),
                    sv.clone(),
                    t.clone(),
                );
                c.info_mut().extend(info.clone());
                c4.push(c);
            }
        }

        let implicit_map = implicits
            .into_iter()
            .map(|(s, t)| (s, SigmaTy::var(t)))
            .collect::<SigmaEnv>();
        let cl5 = InstConstraint::lift(&rhs_aset, &implicit_map)
            .into_iter()
            .map(|(s, mut c)| {
                c.info_mut().extend(info.clone());
                (s, c)
            })
            .collect::<Vec<_>>();

        // A2' = A2\dom(E')
        let rhs_aset = rhs_aset - env.keys();

        let mut m = mono_tys.clone();
        m.extend(cl3.iter().flat_map(|(_, c)| c.free_vars()).cloned());

        // (Cl1 ≪◦ (Cl2 ≥◦ (Cl3 ≥◦ TC1)))

        // cl3 spread with lhs_tree
        let mut tsub0 = lhs_tree.spread_list(cl3);

        // (Cl1 ≪◦ (Cl2 ≥◦ T0))
        // cl2 spread with tsub0
        tsub0 = tsub0.spread_list(cl2);

        // (Cl1 ≪◦ T0)
        // cl strict spread with tsub0
        tsub0 = tsub0.strict_spread_list(cl1);

        // T0 ≪ C4• ≪ (Cl5 ≪◦ TC2)
        let tsub1 = ConstraintTree::list(c4);

        // T0 ≪ T1 ≪ (Cl5 ≪◦ TC2)
        let tsub2 = rhs_tree.strict_spread_list(cl5);

        // T0 ≪ (T1 ≪ T2)
        let tsub3 = StrictTree::new(tsub1, tsub2);

        // T0 ≪ T3
        let tree = StrictTree::new(tsub0, tsub3);

        let mut aset = lhs_aset.clone();
        aset.extend(rhs_aset);

        log::debug!("new aset: {:?}", aset);
        (m, aset, tree)
    }
}
