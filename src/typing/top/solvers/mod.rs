mod greedy;

pub use greedy::*;

use std::collections::HashMap;

use crate::typing::{ty::Ty, ApplySubst};

use super::{
    constraints::{
        Constraint, ConstraintKind, EqConstraint, GenConstraint, ImplicitConstraint,
        InstConstraint, SkolConstraint,
    },
    traits::{Generalize, HasBasic, HasState, HasSubst, PolymorphismInfo, Skolemize},
};

pub trait Solver: HasBasic + HasSubst + HasState {
    fn start_solving(&mut self) -> Result<(), String> {
        while let Some(c) = self.pop_constraint() {
            // self.add_check(c.syntax(), c.semantics());
            println!("solving constraint: {:?}", c);
            self.solve(c)?;
            self.apply_subst();
        }
        Ok(())
    }

    fn solve(&mut self, c: Constraint) -> Result<(), String> {
        match c.kind {
            ConstraintKind::Eq(EqConstraint(s, t)) => self.unify_terms(&s, &t)?,
            ConstraintKind::Gen(GenConstraint(m, v, t)) => {
                self.make_consistent();
                let m = m.apply_subst(self.get_subst());
                println!("t = {}", t);
                let t = t.apply_subst(self.get_subst());
                let s = t.generalize(&m);
                println!("generalized t = {}", s);
                println!("{} => {}", v, s);
                self.store_ty(v, s, c.info);
            }
            ConstraintKind::Inst(InstConstraint(t, r)) => {
                let s = self.find_ty(&r);
                println!("{} => {}", r, s);
                let mut subst = HashMap::new();
                let t_sub = self.instantiate(s, &mut subst);
                println!("instantiate: {}", t_sub);
                let info = c.info.inst_ty(&t); // self.mk_info(&t, c.info);
                self.add_constraint(Constraint {
                    kind: ConstraintKind::Eq(EqConstraint(t, t_sub)),
                    info,
                });
            }
            ConstraintKind::Skol(SkolConstraint(tyvars, t, r)) => {
                let s = self.find_ty(&r);
                let (t_sub, skolems) = s.skolemize();
                let info = c.info.skol_ty(&s);
                self.add_skolems(&info, skolems, tyvars);
                self.add_constraint(Constraint {
                    kind: ConstraintKind::Eq(EqConstraint(t, t_sub)),
                    info,
                });
            }
            ConstraintKind::Implicit(ImplicitConstraint(tyvars, t1, t2)) => {
                let sv = self.next_svar();

                // {(τ1 ≤M τ2) ⟨i⟩} => {σv := Gen(M,τ2), τ1 := Inst(σv)}

                self.add_constraints(vec![
                    Constraint {
                        kind: ConstraintKind::Inst(InstConstraint(t1, Ty::Var(sv.clone()))),
                        info: c.info.clone(),
                    },
                    Constraint {
                        kind: ConstraintKind::Gen(GenConstraint(
                            tyvars.into_iter().map(|tv| Ty::Var(tv.clone())).collect(),
                            sv,
                            t2,
                        )),
                        info: c.info,
                    },
                ]);
            }
        };

        Ok(())
    }
}
