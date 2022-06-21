use std::collections::{HashMap, HashSet, VecDeque};

use crate::typing::ty::TyVar;

use super::Constraint;

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
            todo!()
            // match (&lhs.kind, &rhs.kind) {
            //     (
            //         ConstraintKind::Eq(EqConstraint(lhs_a, lhs_b)),
            //         ConstraintKind::Eq(EqConstraint(rhs_a, rhs_b)),
            //     ) => {
            //         if matches!((lhs_a, rhs_a), (Ty::Var(lhs_tv), Ty::Var(rhs_tv)) if lhs_tv == rhs_tv)
            //         {
            //             Some(Side::Left)
            //         } else if matches!((lhs_b, rhs_b), (Ty::Var(lhs_tv), Ty::Var(rhs_tv)) if lhs_tv == rhs_tv)
            //         {
            //             Some(Side::Right)
            //         } else {
            //             None
            //         }
            //     }
            //     _ => None,
            // }
        }

        // let mut i = 0;
        // while i < self.constraints.len() {
        //     let lhs_id = self.constraints[i];
        //     if !matches!(
        //         &self.index.get(&lhs_id).unwrap().kind,
        //         ConstraintKind::Eq(_)
        //     ) {
        //         i += 1;
        //         continue;
        //     }

        //     let mut lhs_cs = vec![];
        //     let mut rhs_cs = vec![];
        //     let mut j = i + 1;
        //     while j < self.constraints.len() {
        //         let rhs_id = self.constraints[j];
        //         if !matches!(
        //             &self.index.get(&rhs_id).unwrap().kind,
        //             ConstraintKind::Eq(_)
        //         ) {
        //             j += 1;
        //             continue;
        //         }

        //         if let Some(side) = cs_match(
        //             &self.index.get(&lhs_id).unwrap(),
        //             &self.index.get(&rhs_id).unwrap(),
        //         ) {
        //             let eq = variant!(self.remove(j).kind, if ConstraintKind::Eq(e));
        //             match side {
        //                 Side::Left => lhs_cs.push(eq),
        //                 Side::Right => rhs_cs.push(eq),
        //             }
        //         }

        //         j += 1;
        //     }

        //     if lhs_cs.len() != 0 {
        //         let EqConstraint(_, t) = variant!(&mut self.index.get_mut(&lhs_id).unwrap().kind, if ConstraintKind::Eq(eq));
        //         for c in lhs_cs {
        //             let (_, u) = c.unpack();
        //             t.union(u);
        //         }
        //         log::debug!("union ty: {}", t);
        //     }

        //     if rhs_cs.len() != 0 {
        //         let EqConstraint(t, _) = variant!(&mut self.index.get_mut(&lhs_id).unwrap().kind, if ConstraintKind::Eq(eq));
        //         for c in rhs_cs {
        //             let (u, _) = c.unpack();
        //             t.union(u);
        //         }
        //         log::debug!("union ty: {}", t);
        //     }

        //     i += 1;
        // }
        todo!()
    }

    fn index_constraint(&mut self, id: u64) {
        todo!()
        // let c = self.index.get(&id).unwrap();
        // let tyvars = c.collect_tyvars();
        // for v in tyvars.iter() {
        //     if let Some(cs) = self.var_map.get_mut(v) {
        //         cs.insert(id);
        //     } else {
        //         let mut set = HashSet::new();
        //         set.insert(id);
        //         self.var_map.insert(v.clone(), set);
        //     }
        // }

        // self.reverse_map.insert(id, tyvars.to_set());
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
        todo!()
        // let id = c.id;
        // self.index.insert(id, c);
        // self.index_constraint(id);
        // self.constraints.push_back(id);
    }

    pub fn push_front(&mut self, c: Constraint) {
        todo!()
        // let id = c.id;
        // self.index.insert(id, c);
        // self.index_constraint(id);
        // self.constraints.push_front(id);
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
