use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::{
    ast::Path,
    convert::ToSet,
    sort::{topological::TopologicalSort, SortByIndexSlice},
    span::Source,
    typing::ty::{Ty, TyVar},
};

use super::{
    assumptions::AssumptionSet,
    constraints::{
        tree::{ConstraintTree, NodeTree, StrictTree},
        ConstraintInfo, EqConstraint, GenConstraint, InstConstraint, SkolConstraint,
    },
    state::{TyEnv, TyVarFactory},
    traits::HasFreeVars,
};

pub struct BindingGroupAnalysis<'a> {
    groups: Vec<BindingGroup>,
    sigs: &'a TyEnv,
    svar_factory: &'a mut TyVarFactory,
    mono_tys: &'a HashSet<TyVar>,
}

impl<'a> BindingGroupAnalysis<'a> {
    pub fn new(
        groups: Vec<BindingGroup>,
        sigs: &'a TyEnv,
        svar_factory: &'a mut TyVarFactory,
        mono_tys: &'a HashSet<TyVar>,
    ) -> BindingGroupAnalysis<'a> {
        BindingGroupAnalysis {
            groups,
            sigs,
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
                    x.is_mutually_recursive(y, self.sigs)
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
        let sigs = self.sigs;
        let mut ts = TopologicalSort::<usize>::new();
        for ((i, lhs), (j, rhs)) in self.groups.iter().enumerate().tuple_combinations() {
            let (lhs_sigs, lhs_use, _) = lhs.borrow();
            let (rhs_sigs, rhs_use, _) = rhs.borrow();

            if lhs_sigs
                .keys()
                .any(|p| rhs_use.contains_key(p) && !sigs.contains_key(p))
            {
                // LHS defines variables used in RHS, so RHS depends on LHS
                ts.add_dependency(i, j);
            }

            if rhs_sigs
                .keys()
                .any(|p| lhs_use.contains_key(p) && !sigs.contains_key(p))
            {
                // RHS defines variables used in LHS, LHS depends on RHS
                ts.add_dependency(j, i);
            }
        }

        let mut indices = ts.collect::<Vec<_>>();
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
        self.organize_groups();

        let mut mono_tys = self.mono_tys.clone();
        let mut aset = AssumptionSet::new();
        let mut ctree = ConstraintTree::empty();
        while let Some(g) = self.groups.pop() {
            let (new_m, new_a, new_t) =
                g.combine_with(&mono_tys, aset, ctree, self.sigs, self.svar_factory);
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
    info: ConstraintInfo,
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
            info: ConstraintInfo::new(),
        }
    }

    pub fn empty() -> BindingGroup {
        BindingGroup {
            env: TyEnv::new(),
            aset: AssumptionSet::new(),
            ctree: ConstraintTree::empty(),
            info: ConstraintInfo::new(),
        }
    }

    pub fn with_src(mut self, src: Source) -> BindingGroup {
        self.info.src.push(src);
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

    pub fn is_mutually_recursive(&self, other: &BindingGroup, sigs: &HashMap<Path, Ty>) -> bool {
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

        self.info.src.extend(rhs_info.src);
        self.info.src.sort();
        self.info.src.dedup();
    }

    pub fn combine_with(
        self,
        mono_tys: &HashSet<TyVar>,
        rhs_aset: AssumptionSet,
        rhs_tree: ConstraintTree,
        sigs: &TyEnv,
        svar_factory: &mut TyVarFactory,
    ) -> (HashSet<TyVar>, AssumptionSet, ConstraintTree) {
        let info = self.info.clone();
        let env = self.env;
        let lhs_aset = self.aset;
        let lhs_tree = self.ctree;

        // Cl1 = A1 ≼ Σ;
        // We create an instantiation constraint for assumptions in A1
        // for which we have a type scheme in Σ.
        let cl1 = InstConstraint::lift(&lhs_aset, sigs)
            .into_iter()
            .map(|(s, c)| (s, c.with_info(info.clone())))
            .collect::<Vec<_>>();

        // Cl2 = E ≽M Σ;
        // A skolemization constraint is created for each variable in E
        // with a type scheme in Σ. This constraint records the set of
        // monomorphic types passed to bga, and it constrains the type
        // of a definition to be more general than its declared type signature.
        let cl2 = SkolConstraint::lift(&env, sigs, mono_tys)
            .into_iter()
            .map(|(s, c)| (s, c.with_info(info.clone())))
            .collect::<Vec<_>>();

        // A1' = A1\dom(Σ); E' = E\dom(Σ)
        let lhs_aset = lhs_aset.clone() - sigs.keys();
        let env = env.clone() - sigs.keys();

        // Cl3 = A1' ≡ E'
        let cl3 = EqConstraint::lift(&lhs_aset, &env)
            .into_iter()
            .map(|(s, c)| (s, c.with_info(info.clone())))
            .collect::<Vec<_>>();

        // A1'' = A1'\dom(E')
        let lhs_aset = lhs_aset.clone() - env.keys();

        // implicits = zip (dom(E')) [σv1,σv2,...] -- fresh type scheme vars
        let implicits = env
            .keys()
            .sorted()
            .map(|x| (x.clone(), svar_factory.next()))
            .collect::<Vec<_>>();

        let mut c4 = vec![];
        for (x, v) in implicits.iter() {
            if let Some(t) = env.get(x) {
                c4.push(
                    GenConstraint::new(
                        mono_tys.iter().cloned().map(|v| Ty::Var(v)).collect(),
                        v.clone(),
                        t.clone(),
                    )
                    .with_info(info.clone()),
                );
            }
        }

        let implicit_map = implicits
            .into_iter()
            .map(|(s, t)| (s, Ty::Var(t)))
            .collect::<TyEnv>();
        let cl5 = InstConstraint::lift(&rhs_aset, &implicit_map)
            .into_iter()
            .map(|(s, c)| (s, c.with_info(info.clone())))
            .collect::<Vec<_>>();

        // A2' = A2\dom(E')
        let rhs_aset = rhs_aset.clone() - env.keys();

        let mut m = mono_tys.clone();
        m.extend(cl3.free_vars().iter().map(|&t| t.clone()));

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
        let tsub1 = ConstraintTree::list(c4, ConstraintTree::empty());

        // T0 ≪ T1 ≪ (Cl5 ≪◦ TC2)
        let tsub2 = rhs_tree.strict_spread_list(cl5);

        // T0 ≪ (T1 ≪ T2)
        let tsub3 = StrictTree::new(tsub1, tsub2);

        // T0 ≪ T3
        let tree = StrictTree::new(tsub0, tsub3);

        let mut aset = lhs_aset.clone();
        aset.extend(rhs_aset);

        (m, aset, tree)
    }
}
