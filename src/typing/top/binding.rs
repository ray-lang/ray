use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::{
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

fn make_key_set<'a, K: std::cmp::Eq + std::hash::Hash, V, W>(
    map: &'a HashMap<K, V>,
    diff: &'a HashMap<K, W>,
) -> HashSet<&'a K> {
    map.keys()
        .collect::<HashSet<_>>()
        .difference(&diff.keys().collect())
        .map(|&k| k)
        .collect::<HashSet<_>>()
}

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

            let lhs_def_keys = make_key_set(lhs_sigs, sigs);
            let lhs_use_keys = make_key_set(lhs_use, sigs);
            let rhs_def_keys = make_key_set(rhs_sigs, sigs);
            let rhs_use_keys = make_key_set(rhs_use, sigs);

            if !lhs_def_keys.is_disjoint(&rhs_use_keys) {
                // LHS defines variables used in RHS, so RHS depends on LHS
                ts.add_dependency(i, j);
            }

            if !rhs_def_keys.is_disjoint(&lhs_use_keys) {
                // RHS defines variables used in LHS, LHS depends on RHS
                ts.add_dependency(j, i);
            }
        }

        let indices = ts.collect::<Vec<_>>();
        self.groups.sort_by_index_slice(indices);
    }

    pub fn analyze(&mut self) -> (HashSet<TyVar>, AssumptionSet, ConstraintTree) {
        self.organize_groups();

        let mut m = self.mono_tys.clone();
        let mut a = AssumptionSet::new();
        let mut t = ConstraintTree::empty();
        while let Some(g) = self.groups.pop() {
            let (new_m, new_a, new_t) = g.combine_with(&m, &a, &t, self.sigs, self.svar_factory);
            m = new_m;
            a = new_a;
            t = new_t;
        }

        (m, a, t)
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

    pub fn with_info(mut self, info: ConstraintInfo) -> BindingGroup {
        self.info = info;
        self
    }

    pub fn with_src(mut self, src: Option<Source>) -> BindingGroup {
        if let Some(src) = src {
            self.info.src.push(src);
        }
        self
    }

    pub fn unpack(self) -> (TyEnv, AssumptionSet, ConstraintTree) {
        (self.env, self.aset, self.ctree)
    }

    pub fn env(&self) -> &TyEnv {
        &self.env
    }

    pub fn aset(&self) -> &AssumptionSet {
        &self.aset
    }

    pub fn tree(&self) -> &ConstraintTree {
        &self.ctree
    }

    pub fn borrow(&self) -> (&TyEnv, &AssumptionSet, &ConstraintTree) {
        (&self.env, &self.aset, &self.ctree)
    }

    pub fn borrow_mut(&mut self) -> (&mut TyEnv, &mut AssumptionSet, &mut ConstraintTree) {
        (&mut self.env, &mut self.aset, &mut self.ctree)
    }

    pub fn is_mutually_recursive(&self, other: &BindingGroup, sigs: &HashMap<String, Ty>) -> bool {
        let (lhs_sigs, lhs_use, _) = self.borrow();
        let (rhs_sigs, rhs_use, _) = other.borrow();

        let lhs_def_keys = make_key_set(lhs_sigs, sigs);
        let lhs_use_keys = make_key_set(lhs_use, sigs);
        let rhs_def_keys = make_key_set(rhs_sigs, sigs);
        let rhs_use_keys = make_key_set(rhs_use, sigs);

        !lhs_def_keys.is_disjoint(&rhs_use_keys) && !rhs_def_keys.is_disjoint(&lhs_use_keys)
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
        self.info.src.dedup();
    }

    pub fn combine_with(
        &self,
        mono_tys: &HashSet<TyVar>,
        rhs_aset: &AssumptionSet,
        rhs_tree: &ConstraintTree,
        sigs: &TyEnv,
        svar_factory: &mut TyVarFactory,
    ) -> (HashSet<TyVar>, AssumptionSet, ConstraintTree) {
        let info = self.info.clone();
        println!("src: {:?}", info.src);
        let (env, lhs_aset, lhs_tree) = self.borrow();

        // Cl1 = A1 ≼ Σ;
        // We create an instantiation constraint for assumptions in A1
        // for which we have a type scheme in Σ.
        let cl1 = InstConstraint::lift(lhs_aset, sigs)
            .into_iter()
            .map(|(s, c)| (s, c.with_info(info.clone())))
            .collect::<Vec<_>>();

        // Cl2 = E ≽M Σ;
        // A skolemization constraint is created for each variable in E
        // with a type scheme in Σ. This constraint records the set of
        // monomorphic types passed to bga, and it constrains the type
        // of a definition to be more general than its declared type signature.
        let cl2 = SkolConstraint::lift(env, sigs, mono_tys)
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
        let cl5 = InstConstraint::lift(rhs_aset, &implicit_map)
            .into_iter()
            .map(|(s, c)| (s, c.with_info(info.clone())))
            .collect::<Vec<_>>();

        // A2' = A2\dom(E')
        let rhs_aset = rhs_aset.clone() - env.keys();

        let mut m = mono_tys.clone();
        m.extend(cl3.free_vars().iter().map(|&t| t.clone()));

        // (Cl1 ≪◦ (Cl2 ≥◦ (Cl3 ≥◦ TC1)))

        // cl3 spread with lhs_tree
        let mut tsub0 = lhs_tree.clone().spread_list(cl3);

        // (Cl1 ≪◦ (Cl2 ≥◦ T0))
        // cl2 spread with tsub0
        tsub0 = tsub0.spread_list(cl2);

        // (Cl1 ≪◦ T0)
        // cl strict spread with tsub0
        tsub0 = tsub0.strict_spread_list(cl1);

        // T0 ≪ C4• ≪ (Cl5 ≪◦ TC2)
        let tsub1 = ConstraintTree::list(c4, ConstraintTree::empty());

        // T0 ≪ T1 ≪ (Cl5 ≪◦ TC2)
        let tsub2 = rhs_tree.clone().strict_spread_list(cl5);

        // T0 ≪ (T1 ≪ T2)
        let tsub3 = StrictTree::new(tsub1, tsub2);

        // T0 ≪ T3
        let tree = StrictTree::new(tsub0, tsub3);

        let mut aset = lhs_aset.clone();
        aset.extend(rhs_aset);

        (m, aset, tree)
    }
}

#[cfg(test)]
mod binding_tests {
    use std::collections::HashSet;

    use crate::typing::{
        top::{
            assumptions::AssumptionSet,
            constraints::{
                tree::{ConstraintTree, SpreadTree, StrictSpreadTree, StrictTree},
                EqConstraint, GenConstraint, InstConstraint, SkolConstraint,
            },
            state::{TyEnv, TyVarFactory},
        },
        ty::{Ty, TyVar},
    };

    use super::{BindingGroup, BindingGroupAnalysis};

    macro_rules! env {
        {} => (TyEnv::new());

        { $($e:tt : $v:tt),+ } => {{
            let mut env = TyEnv::new();
            $(env.insert(stringify!($e).to_string(), Ty::Var(tvar!($v)));)*
            env
        }};
    }

    macro_rules! BG {
        ( $env:expr, $aset:expr ) => {
            BindingGroup::new($env, $aset, ConstraintTree::empty())
        };
    }

    #[test]
    fn test_combine() {
        let b1 = BG!(env! {}, aset! { x:v0 });
        let b2 = BG!(env! { y:v1 }, aset! { x:v2 });

        let mut b = b1.clone();
        b.combine(b2);
        assert_eq!(b, BG!(env! { y:v1 }, aset! { x:v0, x:v2 }));

        let b1 = BG!(env! { f:v0 }, aset! { x:v1 });
        let b2 = BG!(env! { y:v2 }, aset! { x:v3 });

        let mut b = b1.clone();
        b.combine(b2);
        assert_eq!(b, BG!(env! { f:v0, y:v2 }, aset! { x:v1, x:v3 }));
    }

    #[test]
    fn test_organize() {
        let b1 = BG!(env! {}, aset! { x:v0 });
        let b2 = BG!(env! { f:v1 }, aset! { y:v2 , f:v3 });
        let b3 = BG!(env! { x:v4 }, aset! { g:v5 , x:v6 , y:v7 });
        let b4 = BG!(env! { y:v8 }, aset! { f:v9 , x:v10 , y:v11 , z:v12 });
        let b5 = BG!(env! { g:v13 , h:v14 }, aset! {});

        let b3_4 = BG!(
            env! { y:v8, x:v4 },
            aset! { g:v5 , x:v6 , y:v7, f:v9 , x:v10 , y:v11 , z:v12 }
        );

        let mut sigs = TyEnv::new();
        sigs.insert(
            str!("f"),
            Ty::All(
                vec![tvar!(a)],
                Box::new(Ty::Func(
                    vec![Ty::Var(tvar!(a))],
                    Box::new(Ty::Var(tvar!(a))),
                )),
            ),
        );

        let mut tvar_factory = TyVarFactory::new("v");
        tvar_factory.skip_to(15);
        let mono_tys = HashSet::new();
        let mut bga = BindingGroupAnalysis::new(
            vec![b1.clone(), b2.clone(), b3, b4, b5.clone()],
            &sigs,
            &mut tvar_factory,
            &mono_tys,
        );
        bga.organize_groups();

        for g in bga.groups.iter() {
            println!("{:?}", g);
        }

        assert!(
            bga.groups
                .iter()
                .zip(vec![&b5, &b3_4, &b1, &b2])
                .all(|(a, b)| a == b)
                || bga
                    .groups
                    .iter()
                    .zip(vec![&b5, &b3_4, &b2, &b1])
                    .all(|(a, b)| a == b)
        );
    }

    #[test]
    fn test_analyze() {
        let id_fn_ty = || {
            Ty::All(
                vec![tvar!(a)],
                Box::new(Ty::Func(
                    vec![Ty::Var(tvar!(a))],
                    Box::new(Ty::Var(tvar!(a))),
                )),
            )
        };

        let b1 = BG!(env! {}, aset! { x:v0 });
        let b2 = BG!(env! { f:v1 }, aset! { y:v2 , f:v3 });
        let b3_4 = BG!(
            env! { y:v8, x:v4 },
            aset! { g:v5 , x:v6 , y:v7, f:v9 , x:v10 , y:v11 , z:v12 }
        );
        let b5 = BG!(env! { g:v13 , h:v14 }, aset! {});

        // Σ = [f:∀a.a→a]
        let mut sigs = TyEnv::new();
        sigs.insert(str!("f"), id_fn_ty());

        // let mut bga =
        //     BindingGroupAnalysis::new(vec![b5, b3_4, b1, b2], &sigs, &mut tf, &mono_tys);

        let mut svf = TyVarFactory::new("s");
        let mono_tys = HashSet::new();
        let aset = AssumptionSet::new();
        let ctree = ConstraintTree::empty();

        // We start our binding group analysis with B2, which is the
        // last triple in the ordered list. Two new labeled constraints
        // are created using f's type signature in Σ, because f is in
        // the pattern environment and in the assumption set.
        let (mono_tys, aset, ctree) = b2.combine_with(&mono_tys, &aset, &ctree, &sigs, &mut svf);

        // TcA = (l(v3), v3 := Inst(∀a.a → a))
        //      ≪◦ (l(v1), v1 := Skol(M, ∀a.a → a)) ◃◦ Tc2
        let actual_tree = StrictSpreadTree::new(
            str!("f"),
            InstConstraint::new(Ty::Var(tvar!(v3)), id_fn_ty()),
            SpreadTree::new(
                str!("f"),
                SkolConstraint::new(vec![], Ty::Var(tvar!(v1)), id_fn_ty()),
                ConstraintTree::empty(),
            ),
        );

        assert_eq!(ctree, actual_tree);

        // A = [y:v2]
        assert_eq!(aset, aset! {y: v2});

        // TcB = Tc1 ≪ TcA
        let tc1 = b1.tree().clone();
        let (mono_tys, aset, ctree) = b1.combine_with(&mono_tys, &aset, &ctree, &sigs, &mut svf);

        let actual_tree = StrictTree::new(tc1, actual_tree);
        assert_eq!(ctree, actual_tree);

        // A = [x:v0, y:v2]
        assert_eq!(aset, aset! { x:v0, y:v2 });

        // Next, we consider the combined triples of B3 and B4.
        // At this point, various things happen. The type variable
        // v9 must be an instance of f's type signature, and an
        // equality constraint is generated for all uses of x in
        // B3 and B4, and also for y. Because x and y do not have
        // an explicit type signature, we assign two fresh type
        // scheme variables to them, and create two generalization
        // constraints. Finally, the assumptions about x and y in
        // Ab must be instances of the generalized types of x and y,
        // respectively. Hence, we get the following constraint tree
        let tc3_4 = b3_4.tree().clone();
        let mono_ty_vec = mono_tys
            .clone()
            .into_iter()
            .map(|t| Ty::Var(t))
            .collect::<Vec<_>>();
        let (mono_tys, aset, ctree) = b3_4.combine_with(&mono_tys, &aset, &ctree, &sigs, &mut svf);

        let actual_tree = StrictTree::new(
            // TcC = (
            //     ( l(v9), v9 := Inst(∀a.a → a) ) ≪◦
            //     ([ (l(v6), v4 ≡ v6), (l(v10), v4 ≡ v10), (l(v7), v8 ≡ v7), (l(v11), v8 ≡ v11) ] ≥◦ [Tc3, Tc4])
            // )
            tc3_4
                .spread_list(vec![
                    (
                        str!("x"),
                        EqConstraint::new(Ty::Var(tvar!(v4)), Ty::Var(tvar!(v10))),
                    ),
                    (
                        str!("x"),
                        EqConstraint::new(Ty::Var(tvar!(v4)), Ty::Var(tvar!(v6))),
                    ),
                    (
                        str!("y"),
                        EqConstraint::new(Ty::Var(tvar!(v8)), Ty::Var(tvar!(v11))),
                    ),
                    (
                        str!("y"),
                        EqConstraint::new(Ty::Var(tvar!(v8)), Ty::Var(tvar!(v7))),
                    ),
                ])
                .strict_spread_list(vec![(
                    str!("f"),
                    InstConstraint::new(Ty::Var(tvar!(v9)), id_fn_ty()),
                )]),
            // ≪
            StrictTree::new(
                // [ (l(v4), s0 := Gen(M,v4)), (l(v8), s1 := Gen(M,v8)) ]•
                ConstraintTree::list(
                    vec![
                        GenConstraint::new(mono_ty_vec.clone(), tvar!(s0), Ty::Var(tvar!(v4))),
                        GenConstraint::new(mono_ty_vec.clone(), tvar!(s1), Ty::Var(tvar!(v8))),
                    ],
                    ConstraintTree::empty(),
                ),
                // ≪ ([ (l(v0), v0 := Inst(s0)), (l(v2), v2 := Inst(s1))] ≪◦ TcB)
                actual_tree.strict_spread_list(vec![
                    (
                        str!("x"),
                        InstConstraint::new(Ty::Var(tvar!(v0)), Ty::Var(tvar!(s0))),
                    ),
                    (
                        str!("y"),
                        InstConstraint::new(Ty::Var(tvar!(v2)), Ty::Var(tvar!(s1))),
                    ),
                ]),
            ),
        );

        assert_eq!(ctree, actual_tree);

        // A = [g:v5, z:v12]
        assert_eq!(aset, aset! { g:v5, z:v12 });

        // The last binding group to deal with is B5. This group defines g and h,
        // which we assign the type scheme variables σ2 and σ3, respectively.
        // We create an instantiation constraint for the assumption about g in A

        let tc5 = b5.tree().clone();
        let mono_ty_vec = mono_tys
            .clone()
            .into_iter()
            .map(|t| Ty::Var(t))
            .collect::<Vec<_>>();
        let (_, aset, ctree) = b5.combine_with(&mono_tys, &aset, &ctree, &sigs, &mut svf);

        let actual_tree = StrictTree::new(
            // Tc5 ≪
            tc5,
            StrictTree::new(
                // [(l(v13), σ2 := Gen(M,v13)), (l(v14), σ3 := Gen(M,v14))]• ≪
                ConstraintTree::list(
                    vec![
                        GenConstraint::new(mono_ty_vec.clone(), tvar!(s2), Ty::Var(tvar!(v13))),
                        GenConstraint::new(mono_ty_vec.clone(), tvar!(s3), Ty::Var(tvar!(v14))),
                    ],
                    ConstraintTree::empty(),
                ),
                // ((l(v5), v5 := Inst(σ2)) ≪◦ TcC)
                actual_tree.strict_spread_list(vec![(
                    str!("g"),
                    InstConstraint::new(Ty::Var(tvar!(v5)), Ty::Var(tvar!(s2))),
                )]),
            ),
        );

        assert_eq!(ctree, actual_tree);

        // A = [z:v12]
        assert_eq!(aset, aset! { z:v12 })
    }
}
