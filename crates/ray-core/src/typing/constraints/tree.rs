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

#[allow(dead_code)]
impl PhaseMap {
    pub fn new<T: Into<ConstraintTree>>(v: Vec<(u64, T)>) -> PhaseMap {
        PhaseMap(v.into_iter().map(|(p, t)| (p, t.into())).collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn list(cs: Vec<Constraint>, t: ConstraintTree) -> ConstraintTree {
        cs.into_iter()
            .rfold(t, |t, c| ConstraintTree::Attach(AttachTree(c, Box::new(t))))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseTree(pub u64, pub Box<ConstraintTree>);

impl Into<ConstraintTree> for PhaseTree {
    fn into(self) -> ConstraintTree {
        ConstraintTree::Phase(self)
    }
}

impl PhaseTree {
    #[allow(dead_code)]
    pub fn new<T: Into<ConstraintTree>>(p: u64, t: T) -> ConstraintTree {
        ConstraintTree::Phase(PhaseTree(p, Box::new(t.into())))
    }
}

#[derive(Clone, PartialEq, Eq)]
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
        v.into_iter().rfold(ConstraintTree::empty(), |t2, (_, t1)| {
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

    pub fn from_vec(ctrees: Vec<ConstraintTree>) -> ConstraintTree {
        let mut ct = ConstraintTree::empty();
        for t in ctrees.into_iter().rev() {
            let nodes = if ct.is_empty() { vec![t] } else { vec![t, ct] };
            ct = NodeTree::new::<ConstraintTree>(nodes);
        }
        ct
    }

    pub fn list(cs: Vec<Constraint>) -> ConstraintTree {
        cs.into_iter().rfold(ConstraintTree::empty(), |t, c| {
            ConstraintTree::new(AttachTree(c, Box::new(t)))
        })
    }

    #[allow(dead_code)]
    pub fn labeled_list(cs: Vec<(String, Constraint)>, t: ConstraintTree) -> ConstraintTree {
        cs.into_iter().rfold(t, |t, (l, c)| {
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
        let old = self.clone();
        *self = f(old).into();
    }

    pub fn flatten<W>(self, walker: W) -> Vec<Constraint>
    where
        W: TreeWalk,
    {
        self.flatten_top(walker)
    }

    fn flatten_top<W>(self, walker: W) -> Vec<Constraint>
    where
        W: TreeWalk,
    {
        let pair = self.flatten_rec(walker, vec![]);
        walker.walk(vec![], vec![pair])
    }

    fn flatten_rec<W>(self, walker: W, down: Vec<Constraint>) -> (Vec<Constraint>, Vec<Constraint>)
    where
        W: TreeWalk,
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
            ConstraintTree::StrictSpread(StrictSpreadTree(l, c, t)) => {
                log::debug!("({}, {:?})", l, c);
                let t = ConstraintTree::Strict(StrictTree(
                    Box::new(AttachTree(c, Box::new(ConstraintTree::empty())).into()),
                    t,
                ));
                t.flatten_rec(walker, down)
            }
            ConstraintTree::Receiver(ReceiverTree(l)) => {
                log::debug!("receiver: {}", l);
                ConstraintTree::empty().flatten_rec(walker, down)
            }
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

    /// Specialized non-recursive flatten for BottomUpWalk. This mirrors the
    /// semantics of `flatten(BottomUpWalk)` but avoids deep recursion on the
    /// call stack by using an explicit stack of frames and accumulating the
    /// (cset, up) pairs that BottomUpWalk expects.
    pub fn flatten_bottom_up(self) -> Vec<Constraint> {
        #[derive(Debug)]
        enum FlattenFrame {
            RecEval(ConstraintTree, Vec<Constraint>),
            NodeDone(usize, Vec<Constraint>),
            ParentAttachDone(Constraint),
            StrictDone(Vec<Constraint>),
        }

        let mut stack: Vec<FlattenFrame> = Vec::new();
        let mut results: Vec<(Vec<Constraint>, Vec<Constraint>)> = Vec::new();

        stack.push(FlattenFrame::RecEval(self, Vec::new()));

        fn bottom_up(
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

        while let Some(frame) = stack.pop() {
            match frame {
                FlattenFrame::RecEval(tree, down) => match tree {
                    ConstraintTree::Node(NodeTree(trees)) => {
                        let n = trees.len();
                        stack.push(FlattenFrame::NodeDone(n, down));
                        for child in trees.into_iter().rev() {
                            stack.push(FlattenFrame::RecEval(child, Vec::new()));
                        }
                    }
                    ConstraintTree::Attach(AttachTree(c, t)) => {
                        let mut new_down = down;
                        new_down.push(c);
                        stack.push(FlattenFrame::RecEval(*t, new_down));
                    }
                    ConstraintTree::ParentAttach(ParentAttachTree(c, t)) => {
                        stack.push(FlattenFrame::ParentAttachDone(c));
                        stack.push(FlattenFrame::RecEval(*t, down));
                    }
                    ConstraintTree::Strict(StrictTree(t1, t2)) => {
                        stack.push(FlattenFrame::StrictDone(down));
                        stack.push(FlattenFrame::RecEval(*t2, Vec::new()));
                        stack.push(FlattenFrame::RecEval(*t1, Vec::new()));
                    }
                    ConstraintTree::Spread(SpreadTree(_, c, t)) => {
                        // Spread rewrites to an Attach with the same effect for BottomUpWalk.
                        let mut new_down = down;
                        new_down.push(c);
                        stack.push(FlattenFrame::RecEval(*t, new_down));
                    }
                    ConstraintTree::StrictSpread(StrictSpreadTree(_, c, t)) => {
                        // StrictSpread(l, c, t) rewrites to Strict(Attach(c, empty), t).
                        // Evaluate Attach(c, empty) and t1, then combine as in Strict.
                        stack.push(FlattenFrame::StrictDone(down));
                        stack.push(FlattenFrame::RecEval(*t, Vec::new()));
                        // Attach(c, empty)
                        let attach_tree = ConstraintTree::Attach(AttachTree(
                            c,
                            Box::new(ConstraintTree::empty()),
                        ));
                        stack.push(FlattenFrame::RecEval(attach_tree, Vec::new()));
                    }
                    ConstraintTree::Receiver(ReceiverTree(_)) => {
                        // ReceiverTree behaves like an empty tree under flatten: it
                        // forwards to flatten(empty, down).
                        let empty = ConstraintTree::empty();
                        stack.push(FlattenFrame::RecEval(empty, down));
                    }
                    ConstraintTree::Phase(PhaseTree(_, t)) => {
                        // Phase nodes are transparent to flatten; forward to child.
                        stack.push(FlattenFrame::RecEval(*t, down));
                    }
                },
                FlattenFrame::NodeDone(n, down) => {
                    let mut pairs = Vec::with_capacity(n);
                    for _ in 0..n {
                        pairs.push(results.pop().expect("missing child pair for NodeDone"));
                    }
                    pairs.reverse();

                    let cset = bottom_up(down, pairs);
                    results.push((cset, Vec::new()));
                }
                FlattenFrame::ParentAttachDone(c) => {
                    let (cset, mut up) = results
                        .pop()
                        .expect("missing child pair for ParentAttachDone");
                    up.push(c);
                    results.push((cset, up));
                }
                FlattenFrame::StrictDone(down) => {
                    let (cset2, up2) = results.pop().expect("missing right pair for StrictDone");
                    let (cset1, up1) = results.pop().expect("missing left pair for StrictDone");

                    // For Strict, we first compute cs1 = cset1 + up1 and cs2 = cset2 + up2,
                    // then treat their concatenation as a single "child" for BottomUpWalk,
                    // with no additional up-constraints.
                    let mut cset = Vec::new();
                    cset.extend(cset1);
                    cset.extend(up1);
                    cset.extend(cset2);
                    cset.extend(up2);
                    cset.extend(down);
                    results.push((cset, Vec::new()));
                }
            }
        }

        // Use the same semantics as the original recursive flatten(BottomUpWalk):
        // we expect a single (cset, up) pair at the top and return cset ++ up.
        let (mut cset, up) = results
            .pop()
            .expect("flatten_bottom_up: no result produced");
        cset.extend(up);
        cset
    }

    pub fn spread(self) -> ConstraintTree {
        let mut list: Vec<(String, Constraint)> = Vec::new();

        // Non-recursive version of `spread_with`: walk the tree explicitly with a
        // stack, mutating `list` in the same order as the original recursive
        // implementation, and rebuild an equivalent ConstraintTree.
        #[derive(Debug)]
        enum SpreadFrame {
            Eval(ConstraintTree),
            NodeDone(usize),
            AttachDone(Constraint),
            ParentAttachDone(Constraint),
            StrictDone,
            PhaseDone(u64),
        }

        let mut stack: Vec<SpreadFrame> = Vec::new();
        let mut results: Vec<ConstraintTree> = Vec::new();

        stack.push(SpreadFrame::Eval(self));

        while let Some(frame) = stack.pop() {
            match frame {
                SpreadFrame::Eval(tree) => match tree {
                    ConstraintTree::Node(NodeTree(trees)) => {
                        let n = trees.len();
                        stack.push(SpreadFrame::NodeDone(n));
                        // Process children left-to-right: push in reverse so the
                        // leftmost child is evaluated first.
                        for child in trees.into_iter().rev() {
                            stack.push(SpreadFrame::Eval(child));
                        }
                    }
                    ConstraintTree::Attach(AttachTree(c, t)) => {
                        stack.push(SpreadFrame::AttachDone(c));
                        stack.push(SpreadFrame::Eval(*t));
                    }
                    ConstraintTree::ParentAttach(ParentAttachTree(c, t)) => {
                        stack.push(SpreadFrame::ParentAttachDone(c));
                        stack.push(SpreadFrame::Eval(*t));
                    }
                    ConstraintTree::Strict(StrictTree(t1, t2)) => {
                        // Evaluate left then right on the same `list`, as in the
                        // recursive version.
                        stack.push(SpreadFrame::StrictDone);
                        stack.push(SpreadFrame::Eval(*t2));
                        stack.push(SpreadFrame::Eval(*t1));
                    }
                    ConstraintTree::Spread(SpreadTree(l, c, t))
                    | ConstraintTree::StrictSpread(StrictSpreadTree(l, c, t)) => {
                        log::debug!("spread tree: ({}, {:?})", l, c);
                        list.insert(0, (l, c));
                        stack.push(SpreadFrame::Eval(*t));
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

                        if !cs.is_empty() {
                            results.push(ConstraintTree::list(cs));
                        } else {
                            results.push(ConstraintTree::Receiver(ReceiverTree(l)));
                        }
                    }
                    ConstraintTree::Phase(PhaseTree(i, t)) => {
                        stack.push(SpreadFrame::PhaseDone(i));
                        stack.push(SpreadFrame::Eval(*t));
                    }
                },
                SpreadFrame::NodeDone(n) => {
                    let mut children = Vec::with_capacity(n);
                    for _ in 0..n {
                        children.push(results.pop().expect("missing child for NodeDone"));
                    }
                    children.reverse();
                    results.push(ConstraintTree::Node(NodeTree(children)));
                }
                SpreadFrame::AttachDone(c) => {
                    let child = results.pop().expect("missing child for AttachDone");
                    results.push(ConstraintTree::Attach(AttachTree(c, Box::new(child))));
                }
                SpreadFrame::ParentAttachDone(c) => {
                    let child = results.pop().expect("missing child for ParentAttachDone");
                    results.push(ConstraintTree::ParentAttach(ParentAttachTree(
                        c,
                        Box::new(child),
                    )));
                }
                SpreadFrame::StrictDone => {
                    let right = results.pop().expect("missing right child for StrictDone");
                    let left = results.pop().expect("missing left child for StrictDone");
                    results.push(ConstraintTree::Strict(StrictTree(
                        Box::new(left),
                        Box::new(right),
                    )));
                }
                SpreadFrame::PhaseDone(i) => {
                    let child = results.pop().expect("missing child for PhaseDone");
                    results.push(ConstraintTree::Phase(PhaseTree(i, Box::new(child))));
                }
            }
        }

        let ct = results.pop().expect("spread: no result tree produced");

        if !list.is_empty() {
            panic!(
                "COMPILER ERROR!!!\nnon-empty spread list (missing ReceiveTrees for the following type variables): {:#?}",
                list
            );
        }
        ct
    }

    pub fn spread_rec(self) -> ConstraintTree {
        let mut list = vec![];
        let ct = self.spread_with(&mut list);
        if list.len() != 0 {
            panic!(
                "COMPILER ERROR!!!\nnon-empty spread list (missing ReceiveTrees for the following type variables): {:#?}",
                list
            );
        }
        ct
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
                log::debug!("spread tree: ({}, {:?})", l, c);
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
                    ConstraintTree::list(cs)
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
        // Iterative version of the phase pass: produce (t, pm) where t is the
        // transformed tree and pm is the accumulated PhaseMap, then wrap as
        // before into a PhaseMap with the root at phase index 5.
        #[derive(Debug)]
        enum PhaseFrame {
            Eval(ConstraintTree),
            NodeDone(usize),
            AttachDone(Constraint),
            ParentAttachDone(Constraint),
            StrictDone,
            SpreadDone(String, Constraint),
            StrictSpreadDone(String, Constraint),
            PhaseBubble(u64),
        }

        let mut stack: Vec<PhaseFrame> = Vec::new();
        let mut results: Vec<(ConstraintTree, PhaseMap)> = Vec::new();

        stack.push(PhaseFrame::Eval(self));

        while let Some(frame) = stack.pop() {
            match frame {
                PhaseFrame::Eval(tree) => match tree {
                    ConstraintTree::Node(NodeTree(trees)) => {
                        let n = trees.len();
                        stack.push(PhaseFrame::NodeDone(n));
                        for child in trees.into_iter().rev() {
                            stack.push(PhaseFrame::Eval(child));
                        }
                    }
                    ConstraintTree::Attach(AttachTree(c, t)) => {
                        stack.push(PhaseFrame::AttachDone(c));
                        stack.push(PhaseFrame::Eval(*t));
                    }
                    ConstraintTree::ParentAttach(ParentAttachTree(c, t)) => {
                        stack.push(PhaseFrame::ParentAttachDone(c));
                        stack.push(PhaseFrame::Eval(*t));
                    }
                    ConstraintTree::Strict(StrictTree(t1, t2)) => {
                        stack.push(PhaseFrame::StrictDone);
                        stack.push(PhaseFrame::Eval(*t2));
                        stack.push(PhaseFrame::Eval(*t1));
                    }
                    ConstraintTree::Spread(SpreadTree(l, c, t)) => {
                        stack.push(PhaseFrame::SpreadDone(l, c));
                        stack.push(PhaseFrame::Eval(*t));
                    }
                    ConstraintTree::StrictSpread(StrictSpreadTree(l, c, t)) => {
                        stack.push(PhaseFrame::StrictSpreadDone(l, c));
                        stack.push(PhaseFrame::Eval(*t));
                    }
                    ConstraintTree::Receiver(ReceiverTree(l)) => {
                        results.push((ConstraintTree::Receiver(ReceiverTree(l)), PhaseMap(vec![])));
                    }
                    ConstraintTree::Phase(PhaseTree(i, t)) => {
                        stack.push(PhaseFrame::PhaseBubble(i));
                        stack.push(PhaseFrame::Eval(*t));
                    }
                },
                PhaseFrame::NodeDone(n) => {
                    let mut trees = Vec::with_capacity(n);
                    let mut pm_acc = PhaseMap(vec![]);
                    for _ in 0..n {
                        let (tree, pm) = results.pop().expect("missing child result for NodeDone");
                        trees.push(tree);
                        pm_acc = pm_acc + pm;
                    }
                    trees.reverse();
                    results.push((NodeTree(trees).into(), pm_acc));
                }
                PhaseFrame::AttachDone(c) => {
                    let (child, pm) = results.pop().expect("missing child result for AttachDone");
                    results.push((AttachTree(c, Box::new(child)).into(), pm));
                }
                PhaseFrame::ParentAttachDone(c) => {
                    let (child, pm) = results
                        .pop()
                        .expect("missing child result for ParentAttachDone");
                    results.push((ParentAttachTree(c, Box::new(child)).into(), pm));
                }
                PhaseFrame::StrictDone => {
                    let (t2, pm2) = results
                        .pop()
                        .expect("missing right child result for StrictDone");
                    let (t1, pm1) = results
                        .pop()
                        .expect("missing left child result for StrictDone");

                    // Original behavior calls `phase` on each child subtree, which is
                    // equivalent to wrapping them via `ConstraintTree::from` with a
                    // PhaseMap carrying their own root at index 5 plus any accumulated
                    // phase entries.
                    let left = ConstraintTree::from(PhaseMap(vec![(5, t1)]) + pm1);
                    let right = ConstraintTree::from(PhaseMap(vec![(5, t2)]) + pm2);
                    results.push((
                        StrictTree(Box::new(left), Box::new(right)).into(),
                        PhaseMap(vec![]),
                    ));
                }
                PhaseFrame::SpreadDone(l, c) => {
                    let (t_prime, pm) = results.pop().expect("missing child result for SpreadDone");
                    results.push((SpreadTree(l, c, Box::new(t_prime)).into(), pm));
                }
                PhaseFrame::StrictSpreadDone(l, c) => {
                    let (t_prime, pm) = results
                        .pop()
                        .expect("missing child result for StrictSpreadDone");
                    let inner = ConstraintTree::from(PhaseMap(vec![(5, t_prime)]) + pm);
                    results.push((
                        StrictSpreadTree(l, c, Box::new(inner)).into(),
                        PhaseMap(vec![]),
                    ));
                }
                PhaseFrame::PhaseBubble(i) => {
                    let (t_prime, pm) =
                        results.pop().expect("missing child result for PhaseBubble");
                    let pm_new = PhaseMap(vec![(i, t_prime)]) + pm;
                    results.push((ConstraintTree::empty(), pm_new));
                }
            }
        }

        let (t, pm) = results.pop().expect("phase: no result produced");
        ConstraintTree::from(PhaseMap(vec![(5, t)]) + pm)
    }

    pub fn phase_rec(self) -> ConstraintTree {
        let (t, pm) = self.phase_rec0();
        ConstraintTree::from(PhaseMap(vec![(5, t)]) + pm)
    }

    fn phase_rec0(self) -> (ConstraintTree, PhaseMap) {
        match self {
            ConstraintTree::Node(NodeTree(trees)) => {
                let (trees, pms): (Vec<_>, Vec<_>) =
                    trees.into_iter().map(|t| t.phase_rec0()).unzip();
                (
                    NodeTree(trees).into(),
                    pms.into_iter().rfold(PhaseMap(vec![]), |pm, p0| pm + p0),
                )
            }
            ConstraintTree::Attach(AttachTree(c, t)) => {
                let (t_prime, pm) = t.phase_rec0();
                (AttachTree(c, Box::new(t_prime)).into(), pm)
            }
            ConstraintTree::ParentAttach(ParentAttachTree(c, t)) => {
                let (t_prime, pm) = t.phase_rec0();
                (ParentAttachTree(c, Box::new(t_prime)).into(), pm)
            }
            ConstraintTree::Strict(StrictTree(t1, t2)) => (
                StrictTree(Box::new(t1.phase()), Box::new(t2.phase())).into(),
                PhaseMap(vec![]),
            ),
            ConstraintTree::Spread(SpreadTree(l, c, t)) => {
                let (t_prime, pm) = t.phase_rec0();
                (SpreadTree(l, c, Box::new(t_prime)).into(), pm)
            }
            ConstraintTree::StrictSpread(StrictSpreadTree(l, c, t)) => (
                StrictSpreadTree(l, c, Box::new(t.phase())).into(),
                PhaseMap(vec![]),
            ),
            ConstraintTree::Receiver(ReceiverTree(l)) => (ReceiverTree(l).into(), PhaseMap(vec![])),
            ConstraintTree::Phase(PhaseTree(i, t)) => {
                let (t_prime, pm) = t.phase_rec0();
                (ConstraintTree::empty(), PhaseMap(vec![(i, t_prime)]) + pm)
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct BottomUpWalk;

impl TreeWalk for BottomUpWalk {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing::{
        constraints::{Constraint, EqConstraint},
        ty::Ty,
    };

    fn dummy_constraint(id: u32) -> Constraint {
        EqConstraint::new(Ty::con(id.to_string()), Ty::con(id.to_string()))
    }

    #[test]
    fn flatten_bottom_up_simple_attach() {
        let c1 = dummy_constraint(1);
        let tree =
            ConstraintTree::Attach(AttachTree(c1.clone(), Box::new(ConstraintTree::empty())));
        let cs = tree.spread().phase().flatten_bottom_up();
        assert_eq!(cs, vec![c1]);
    }

    #[test]
    fn flatten_bottom_up_parent_attach() {
        let c1 = dummy_constraint(1);
        let c2 = dummy_constraint(2);
        // ParentAttach(c1, Attach(c2, empty)) should flatten to [c2, c1].
        let child =
            ConstraintTree::Attach(AttachTree(c2.clone(), Box::new(ConstraintTree::empty())));
        let tree = ConstraintTree::ParentAttach(ParentAttachTree(c1.clone(), Box::new(child)));
        let cs = tree.spread().phase().flatten_bottom_up();
        assert_eq!(cs, vec![c2, c1]);
    }

    #[test]
    fn flatten_bottom_up_strict_of_attaches() {
        let c1 = dummy_constraint(1);
        let c2 = dummy_constraint(2);
        let t1 = ConstraintTree::Attach(AttachTree(c1.clone(), Box::new(ConstraintTree::empty())));
        let t2 = ConstraintTree::Attach(AttachTree(c2.clone(), Box::new(ConstraintTree::empty())));
        let tree = ConstraintTree::Strict(StrictTree(Box::new(t1), Box::new(t2)));
        let cs = tree.spread().phase().flatten_bottom_up();
        assert_eq!(cs, vec![c1, c2]);
    }

    #[test]
    fn flatten_bottom_up_spread_behaves_like_attach() {
        let c1 = dummy_constraint(1);
        // A labeled Spread without a matching Receiver will cause `spread()` to
        // panic (by design). Model the intended pipeline by pairing the Spread
        // with a Receiver of the same label so that `spread()` turns the label
        // into an Attach list before flattening.
        let spread = ConstraintTree::Spread(SpreadTree(
            "?x".to_string(),
            c1.clone(),
            Box::new(ConstraintTree::empty()),
        ));
        let recv = ConstraintTree::Receiver(ReceiverTree("?x".to_string()));
        let tree = ConstraintTree::Node(NodeTree(vec![spread, recv]));
        let cs = tree.spread().phase().flatten_bottom_up();
        assert_eq!(cs, vec![c1]);
    }
}
