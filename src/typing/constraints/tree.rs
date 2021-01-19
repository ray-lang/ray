use std::ops::Add;

use crate::typing::traits::TreeWalk;

use super::Constraint;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseMap(Vec<(u64, ConstraintTree)>);

impl Add for PhaseMap {
    type Output = PhaseMap;

    fn add(self, rhs: PhaseMap) -> PhaseMap {
        let PhaseMap(mut v1) = self;
        let PhaseMap(mut v2) = rhs;

        if v1.len() == 0 {
            PhaseMap(v2)
        } else if v2.len() == 0 {
            PhaseMap(v1)
        } else {
            let mut v = vec![];
            loop {
                if v1.len() == 0 {
                    v.extend(v2);
                    break;
                } else if v2.len() == 0 {
                    v.extend(v1);
                    break;
                } else {
                    let (i, _) = v1[0];
                    let (j, _) = v2[0];

                    if i == j {
                        let (_, tx) = v1.remove(0);
                        let (_, ty) = v2.remove(0);
                        v.push((i, NodeTree(vec![tx, ty]).into()));
                    } else if i < j {
                        let (_, tx) = v1.remove(0);
                        v.push((i, tx));
                    } else if i > j {
                        let (_, ty) = v2.remove(0);
                        v.push((j, ty));
                    }
                }
            }

            PhaseMap(v)
        }
    }
}

impl PhaseMap {
    pub fn new<T: Into<ConstraintTree>>(v: Vec<(u64, T)>) -> PhaseMap {
        PhaseMap(v.into_iter().map(|(p, t)| (p, t.into())).collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodeTree(pub Vec<ConstraintTree>);

impl Into<ConstraintTree> for NodeTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::Node(self)
    }
}

impl NodeTree {
    pub fn new<T: Into<ConstraintTree>>(v: Vec<T>) -> ConstraintTree {
        ConstraintTree::Node(NodeTree(v.into_iter().map(|t| t.into()).collect()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AttachTree(pub Constraint, pub Box<ConstraintTree>);

impl Into<ConstraintTree> for AttachTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::Attach(self)
    }
}

impl AttachTree {
    pub fn new<T: Into<ConstraintTree>>(c: Constraint, t: T) -> ConstraintTree {
        ConstraintTree::Attach(AttachTree(c, Box::new(t.into())))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParentAttachTree(pub Constraint, pub Box<ConstraintTree>);

impl Into<ConstraintTree> for ParentAttachTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::ParentAttach(self)
    }
}

impl ParentAttachTree {
    pub fn new<T: Into<ConstraintTree>>(c: Constraint, t: T) -> ConstraintTree {
        ConstraintTree::ParentAttach(ParentAttachTree(c, Box::new(t.into())))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StrictTree(pub Box<ConstraintTree>, pub Box<ConstraintTree>);

impl Into<ConstraintTree> for StrictTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::Strict(self)
    }
}

impl StrictTree {
    pub fn new<A: Into<ConstraintTree>, B: Into<ConstraintTree>>(a: A, b: B) -> ConstraintTree {
        let ct1 = ConstraintTree::new(a);
        let ct2 = ConstraintTree::new(b);

        match (ct1, ct2) {
            (ct1, ct2) if !ct1.is_empty() && !ct2.is_empty() => {
                ConstraintTree::new(StrictTree(Box::new(ct1), Box::new(ct2)))
            }
            (ct1, _) if !ct1.is_empty() => ct1, // ct2 is empty
            (_, ct2) => ct2,                    // ct1 is empty
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SpreadTree(pub String, pub Constraint, pub Box<ConstraintTree>);

impl Into<ConstraintTree> for SpreadTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::Spread(self)
    }
}

impl SpreadTree {
    pub fn new<T: Into<ConstraintTree>>(l: String, c: Constraint, t: T) -> ConstraintTree {
        ConstraintTree::Spread(SpreadTree(l, c, Box::new(t.into())))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StrictSpreadTree(pub String, pub Constraint, pub Box<ConstraintTree>);

impl Into<ConstraintTree> for StrictSpreadTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::StrictSpread(self)
    }
}

impl StrictSpreadTree {
    pub fn new<T: Into<ConstraintTree>>(l: String, c: Constraint, t: T) -> ConstraintTree {
        ConstraintTree::StrictSpread(StrictSpreadTree(l, c, Box::new(t.into())))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReceiverTree(pub String);

impl Into<ConstraintTree> for ReceiverTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::Receiver(self)
    }
}

impl ReceiverTree {
    pub fn new(l: String) -> ConstraintTree {
        ConstraintTree::Receiver(ReceiverTree(l))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PhaseTree(pub u64, pub Box<ConstraintTree>);

impl Into<ConstraintTree> for PhaseTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::Phase(self)
    }
}

impl PhaseTree {
    pub fn new<T: Into<ConstraintTree>>(p: u64, t: T) -> ConstraintTree {
        ConstraintTree::Phase(PhaseTree(p, Box::new(t.into())))
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ConstraintTree {
    Node(NodeTree),
    Attach(AttachTree),
    ParentAttach(ParentAttachTree),
    Strict(StrictTree),
    Spread(SpreadTree),
    StrictSpread(StrictSpreadTree),
    Receiver(ReceiverTree),
    Phase(PhaseTree),
}

impl From<PhaseMap> for ConstraintTree {
    fn from(pm: PhaseMap) -> ConstraintTree {
        let PhaseMap(v) = pm;
        v.into_iter()
            .rev()
            .fold(ConstraintTree::empty(), |t2, (_, t1)| {
                ConstraintTree::new(StrictTree(Box::new(t1), Box::new(t2)))
            })
    }
}

impl std::fmt::Debug for ConstraintTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintTree::Node(c) => write!(f, "{:?}", c),
            ConstraintTree::Attach(c) => write!(f, "{:?}", c),
            ConstraintTree::ParentAttach(c) => write!(f, "{:?}", c),
            ConstraintTree::Strict(c) => write!(f, "{:?}", c),
            ConstraintTree::Spread(c) => write!(f, "{:?}", c),
            ConstraintTree::StrictSpread(c) => write!(f, "{:?}", c),
            ConstraintTree::Receiver(c) => write!(f, "{:?}", c),
            ConstraintTree::Phase(c) => write!(f, "{:?}", c),
        }
    }
}

impl ConstraintTree {
    pub fn new<T: Into<ConstraintTree>>(t: T) -> ConstraintTree {
        t.into()
    }

    pub fn empty() -> ConstraintTree {
        ConstraintTree::new(NodeTree(vec![]))
    }

    pub fn list(cs: Vec<Constraint>, t: ConstraintTree) -> ConstraintTree {
        cs.into_iter()
            .rev()
            .fold(t, |t, c| ConstraintTree::new(AttachTree(c, Box::new(t))))
    }

    pub fn labeled_list(cs: Vec<(String, Constraint)>, t: ConstraintTree) -> ConstraintTree {
        cs.into_iter().rev().fold(t, |t, (l, c)| {
            ConstraintTree::new(SpreadTree(l, c, Box::new(t)))
        })
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, ConstraintTree::Node(NodeTree(v)) if v.len() == 0)
    }

    pub fn replace<F, T>(&mut self, f: F)
    where
        T: Into<ConstraintTree>,
        F: FnOnce(ConstraintTree) -> T,
    {
        let old = std::mem::replace(self, ConstraintTree::empty());
        *self = f(old).into();
    }

    pub fn flatten<W>(self, walker: W) -> Vec<Constraint>
    where
        W: TreeWalk<Constraint>,
    {
        self.flatten_top(walker)
    }

    fn flatten_top<W>(self, walker: W) -> Vec<Constraint>
    where
        W: TreeWalk<Constraint>,
    {
        let pair = self.flatten_rec(walker, vec![]);
        walker.walk(vec![], vec![pair])
    }

    fn flatten_rec<W>(self, walker: W, down: Vec<Constraint>) -> (Vec<Constraint>, Vec<Constraint>)
    where
        W: TreeWalk<Constraint>,
    {
        match self {
            ConstraintTree::Node(NodeTree(trees)) => {
                let pairs = trees
                    .into_iter()
                    .map(|t| t.flatten_rec(walker, vec![]))
                    .collect::<Vec<_>>();

                (walker.walk(down, pairs), vec![])
            }
            ConstraintTree::Attach(AttachTree(c, t)) => {
                let mut down = down;
                down.push(c);
                t.flatten_rec(walker, down)
            }
            ConstraintTree::ParentAttach(ParentAttachTree(c, t)) => {
                let (cset, mut up) = t.flatten_rec(walker, down);
                up.push(c);
                (cset, up)
            }
            ConstraintTree::Strict(StrictTree(t1, t2)) => {
                let mut cs = t1.flatten_top(walker);
                cs.extend(t2.flatten_top(walker));
                (walker.walk(down, vec![(cs, vec![])]), vec![])
            }
            ConstraintTree::Spread(SpreadTree(_, c, t)) => {
                let t = ConstraintTree::Attach(AttachTree(c, t));
                t.flatten_rec(walker, down)
            }
            ConstraintTree::StrictSpread(StrictSpreadTree(_, c, t)) => {
                let t = ConstraintTree::Strict(StrictTree(
                    Box::new(AttachTree(c, Box::new(ConstraintTree::empty())).into()),
                    t,
                ));
                t.flatten_rec(walker, down)
            }
            ConstraintTree::Receiver(_) => ConstraintTree::empty().flatten_rec(walker, down),
            ConstraintTree::Phase(PhaseTree(_, t)) => t.flatten_rec(walker, down),
        }
    }

    pub fn spread_list(self, list: Vec<(String, Constraint)>) -> ConstraintTree {
        list.into_iter()
            .rfold(self, |t, (l, c)| SpreadTree::new(l, c, t))
    }

    pub fn strict_spread_list(self, list: Vec<(String, Constraint)>) -> ConstraintTree {
        list.into_iter()
            .rfold(self, |t, (l, c)| StrictSpreadTree::new(l, c, t))
    }

    pub fn spread(self) -> ConstraintTree {
        self.spread_with(&mut vec![])
    }

    fn spread_with(self, list: &mut Vec<(String, Constraint)>) -> ConstraintTree {
        match self {
            ConstraintTree::Node(NodeTree(trees)) => ConstraintTree::Node(NodeTree(
                trees.into_iter().map(|t| t.spread_with(list)).collect(),
            )),
            ConstraintTree::Attach(AttachTree(c, t)) => {
                ConstraintTree::Attach(AttachTree(c, Box::new(t.spread_with(list))))
            }
            ConstraintTree::ParentAttach(ParentAttachTree(c, t)) => {
                ConstraintTree::ParentAttach(ParentAttachTree(c, Box::new(t.spread_with(list))))
            }
            ConstraintTree::Strict(StrictTree(t1, t2)) => ConstraintTree::Strict(StrictTree(
                Box::new(t1.spread_with(list)),
                Box::new(t2.spread_with(list)),
            )),
            ConstraintTree::Spread(SpreadTree(l, c, t))
            | ConstraintTree::StrictSpread(StrictSpreadTree(l, c, t)) => {
                list.insert(0, (l, c));
                t.spread_with(list)
            }
            ConstraintTree::Receiver(ReceiverTree(l)) => {
                let mut i = 0;
                let mut cs = vec![];
                while i != list.len() {
                    if matches!(&list[i], (l_prime, _) if &l == l_prime) {
                        let (_, c) = list.remove(i);
                        cs.push(c);
                    } else {
                        i += 1;
                    }
                }

                if cs.len() > 0 {
                    ConstraintTree::list(cs, ConstraintTree::empty())
                } else {
                    ConstraintTree::Receiver(ReceiverTree(l))
                }
            }
            ConstraintTree::Phase(PhaseTree(i, t)) => {
                ConstraintTree::Phase(PhaseTree(i, Box::new(t.spread_with(list))))
            }
        }
    }

    pub fn phase(self) -> ConstraintTree {
        let (t, pm) = self.phase_rec();
        ConstraintTree::from(PhaseMap(vec![(5, t)]) + pm)
    }

    fn phase_rec(self) -> (ConstraintTree, PhaseMap) {
        match self {
            ConstraintTree::Node(NodeTree(trees)) => {
                let (trees, pms): (Vec<_>, Vec<_>) =
                    trees.into_iter().map(|t| t.phase_rec()).unzip();
                (
                    NodeTree(trees).into(),
                    pms.into_iter()
                        .rev()
                        .fold(PhaseMap(vec![]), |pm, p0| pm + p0),
                )
            }
            ConstraintTree::Attach(AttachTree(c, t)) => {
                let (t_prime, pm) = t.phase_rec();
                (AttachTree(c, Box::new(t_prime)).into(), pm)
            }
            ConstraintTree::ParentAttach(ParentAttachTree(c, t)) => {
                let (t_prime, pm) = t.phase_rec();
                (ParentAttachTree(c, Box::new(t_prime)).into(), pm)
            }
            ConstraintTree::Strict(StrictTree(t1, t2)) => (
                StrictTree(Box::new(t1.phase()), Box::new(t2.phase())).into(),
                PhaseMap(vec![]),
            ),
            ConstraintTree::Spread(SpreadTree(l, c, t)) => {
                let (t_prime, pm) = t.phase_rec();
                (SpreadTree(l, c, Box::new(t_prime)).into(), pm)
            }
            ConstraintTree::StrictSpread(StrictSpreadTree(l, c, t)) => (
                StrictSpreadTree(l, c, Box::new(t.phase())).into(),
                PhaseMap(vec![]),
            ),
            ConstraintTree::Receiver(ReceiverTree(l)) => (ReceiverTree(l).into(), PhaseMap(vec![])),
            ConstraintTree::Phase(PhaseTree(i, t)) => {
                let (t_prime, pm) = t.phase_rec();
                (ConstraintTree::empty(), PhaseMap(vec![(i, t_prime)]) + pm)
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct BottomUpWalk;

impl TreeWalk<Constraint> for BottomUpWalk {
    fn walk(
        self,
        down: Vec<Constraint>,
        pairs: Vec<(Vec<Constraint>, Vec<Constraint>)>,
    ) -> Vec<Constraint> {
        let mut c = vec![];
        let (csets, ups): (Vec<_>, Vec<_>) = pairs.into_iter().unzip();
        c.extend(csets.into_iter().flatten());
        c.extend(ups.into_iter().flatten());
        c.extend(down);
        c
    }
}

#[derive(Copy, Clone)]
pub struct TopDownWalk;

impl TreeWalk<Constraint> for TopDownWalk {
    fn walk(
        self,
        down: Vec<Constraint>,
        pairs: Vec<(Vec<Constraint>, Vec<Constraint>)>,
    ) -> Vec<Constraint> {
        let mut c = vec![];
        c.extend(down);

        let (csets, ups): (Vec<_>, Vec<_>) = pairs.into_iter().unzip();
        c.extend(ups.into_iter().flatten());
        c.extend(csets.into_iter().flatten());
        c
    }
}

#[cfg(test)]
mod tree_tests {
    use crate::typing::{
        constraints::{EqConstraint, ImplicitConstraint},
        solvers::{GreedySolver, Solver},
        state::TyVarFactory,
        traits::HasSubst,
        ty::{Ty, TyVar},
        Ctx, InferError,
    };

    use super::{BottomUpWalk, ConstraintTree};

    #[test]
    fn test_constraints1() -> Result<(), InferError> {
        let mul = Ty::Func(vec![Ty::int(), Ty::int()], Box::new(Ty::int()));

        // let sq = λx.(x * x) in sq(1)
        let x0 = tvar!(x0); // type of the first x in the body
        let x1 = tvar!(x1); // type of the second x in the body
        let app0 = tvar!(app0); // type of the app

        // constraint: (x0 -> x1 -> r) == mul
        let c1 = EqConstraint::new(
            Ty::Func(
                vec![Ty::Var(x0), Ty::Var(x1)],
                Box::new(Ty::Var(app0.clone())),
            ),
            mul,
        );

        // λx.(x * x)
        let lam0 = tvar!(lam0); // type of the lambda
        let p0 = tvar!(p0); // type of parameter `x`
        let r0 = tvar!(r0); // type of the body
                            // constraint: lam0 == (p0 -> r0)
        let c2 = EqConstraint::new(
            Ty::Var(lam0),
            Ty::Func(vec![Ty::Var(p0.clone())], Box::new(Ty::Var(r0))),
        );

        // constraint: p0 == p1
        let p1 = tvar!(p1);
        let c3 = EqConstraint::new(Ty::Var(p0.clone()), Ty::Var(p1));

        let sq = tvar!(sq); // type of ident `sq`
        let b0 = tvar!(b0); // type of let body
        let l0 = tvar!(l0); // type of let
        let l1 = tvar!(sq0); // type of the let rhs

        // constraint: b0 == l0
        let c4 = EqConstraint::new(Ty::Var(b0), Ty::Var(l0));

        // constraint: sq ≤m l1
        let c5 = ImplicitConstraint::new(vec![p0], Ty::Var(sq), Ty::Var(l1));

        let t = ConstraintTree::list(vec![c1, c2, c3, c4, c5], ConstraintTree::empty());

        let walker = BottomUpWalk {};
        let cs = t.flatten(walker);
        let mut ctx = Ctx::new();
        let mut solver = GreedySolver::new(cs, &mut ctx);
        // solver.solve()?;
        println!("{:#?}", solver.get_subst());
        Ok(())
    }
}
