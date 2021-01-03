use std::collections::HashSet;

use crate::typing::{
    top::{
        assumptions::AssumptionSet,
        binding::{BindingGroup, BindingGroupAnalysis},
        constraints::{
            tree::{
                AttachTree, ConstraintTree, NodeTree, ParentAttachTree, ReceiverTree,
                StrictSpreadTree,
            },
            CollectConstraints, Constraint, EqConstraint,
        },
        state::{TyEnv, TyVarFactory},
    },
    ty::{Ty, TyVar},
};

use super::{Expr, LitKind};

impl CollectConstraints for Expr {
    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Ty, AssumptionSet, ConstraintTree) {
        match self {
            Expr::Lit(k) => {
                let v = Ty::Var(tf.next());
                let t = match k {
                    LitKind::Int => Ty::int(),
                    LitKind::Float => Ty::float(),
                    LitKind::String => Ty::string(),
                    LitKind::Char => Ty::char(),
                };
                let cs = vec![Constraint::new(EqConstraint(v.clone(), t))];
                (
                    v,
                    AssumptionSet::new(),
                    ConstraintTree::list(cs, ConstraintTree::empty()),
                )
            }
            Expr::Var(v) => {
                let t = Ty::Var(tf.next());
                let label = v.to_string();
                let mut aset = AssumptionSet::new();
                aset.add(v.clone(), t.clone());
                (t, aset, ReceiverTree::new(label))
            }
            Expr::App(fun, args) => {
                let mut aset = AssumptionSet::new();
                let (fun_ty, fun_aset, ct1) = fun.collect_constraints(mono_tys, tf);
                aset.extend(fun_aset);

                let mut arg_tys = vec![];
                let mut arg_cts = vec![];

                for (ty, a, ct) in args.iter().map(|a| a.collect_constraints(mono_tys, tf)) {
                    aset.extend(a);
                    arg_tys.push(ty);
                    arg_cts.push(ct);
                }

                let ret_ty = Ty::Var(tf.next());
                let c = Constraint::new(EqConstraint(
                    fun_ty,
                    Ty::Func(arg_tys, Box::new(ret_ty.clone())),
                ));

                let mut cts = vec![ct1];
                cts.extend(arg_cts);

                (ret_ty, aset, AttachTree::new(c, NodeTree::new(cts)))
            }
            Expr::Abs(params, body) => {
                let mut mono_tys = mono_tys.clone();
                let mut param_tys = vec![];
                let mut env = TyEnv::new();
                let mut cts = vec![];
                for p in params {
                    let tv = tf.next();
                    mono_tys.insert(tv.clone());
                    let ty = Ty::Var(tv.clone());
                    cts.push(ReceiverTree::new(p.to_string()));
                    param_tys.push(ty.clone());
                    env.insert(p.clone(), ty);
                }

                let (body_ty, aset, ct) = body.collect_constraints(&mono_tys, tf);
                cts.push(ct);

                let cl = EqConstraint::lift(&aset, &env);
                let ct = cl.into_iter().rfold(NodeTree::new(cts), |ct, (x, c)| {
                    StrictSpreadTree::new(x, c, ct)
                });

                let fun_ty = Ty::Var(tf.next());
                let c = Constraint::new(EqConstraint(
                    fun_ty.clone(),
                    Ty::Func(param_tys, Box::new(body_ty)),
                ));

                (fun_ty, aset - env.keys(), AttachTree::new(c, ct))
            }
            Expr::Cond(cond, then, els) => {
                let (t1, aset1, ct1) = cond.collect_constraints(mono_tys, tf);
                let (t2, aset2, ct2) = then.collect_constraints(mono_tys, tf);
                let (t3, aset3, ct3) = els.collect_constraints(mono_tys, tf);

                let branch_ty = Ty::Var(tf.next());
                let ct = NodeTree::new(vec![
                    ParentAttachTree::new(Constraint::new(EqConstraint(t1, Ty::bool())), ct1),
                    ParentAttachTree::new(
                        Constraint::new(EqConstraint(t2, branch_ty.clone())),
                        ct2,
                    ),
                    ParentAttachTree::new(
                        Constraint::new(EqConstraint(t3, branch_ty.clone())),
                        ct3,
                    ),
                ]);

                let aset = AssumptionSet::from(vec![aset1, aset2, aset3]);

                (branch_ty, aset, ct)
            }
            Expr::Let(var, rhs, body) => {
                let (bg, env) = self.decl_var(var, rhs, mono_tys, tf);
                println!("let: bg = {:?}", bg);
                println!("let: env = {:?}", env);

                let (body_ty, aset, ct) = body.collect_constraints(mono_tys, tf);
                println!("let: body_ty = {}", body_ty);
                println!("let: aset = {:?}", aset);
                println!("let: ct = {:?}", ct);

                let mut bga = BindingGroupAnalysis::new(
                    vec![BindingGroup::new(TyEnv::new(), aset, ct), bg],
                    &env,
                    tf,
                    mono_tys,
                );

                let (_, a, t) = bga.analyze();
                println!("let: bga.a = {:?}", a);
                println!("let: bga.t = {:?}", t);

                let b = Ty::Var(tf.next());
                let c = Constraint::new(EqConstraint(b.clone(), body_ty));
                (b, a, AttachTree::new(c, t))
            }
        }
    }
}

#[derive(Debug)]
pub struct ConstraintCollector<'a> {
    tvar_factory: &'a mut TyVarFactory,
}

#[cfg(test)]
mod collector_tests {
    use std::collections::HashSet;

    use crate::typing::{
        top::{
            assumptions::AssumptionSet,
            constraints::{
                tree::{
                    AttachTree, ConstraintTree, NodeTree, ReceiverTree, StrictSpreadTree,
                    StrictTree,
                },
                CollectConstraints, Constraint, EqConstraint, GenConstraint, InstConstraint,
            },
            hm::{Expr, LitKind},
            state::TyVarFactory,
        },
        ty::{Ty, TyVar},
    };

    macro_rules! aset {
        {} => (AssumptionSet::new());

        { $($e:tt : $v:tt),+ } => {{
            AssumptionSet::from(vec![
                $((stringify!($e).to_string(), Ty::Var(tvar!($v)))),*
            ])
        }};
    }

    #[test]
    fn test_var() {
        let ex = Expr::Var(str!("x"));

        let mut tf = TyVarFactory::new("v");
        let mono_tys = HashSet::new();
        let (t, a, ct) = ex.collect_constraints(&mono_tys, &mut tf);

        assert_eq!(t, Ty::Var(tvar!(v0)));
        assert_eq!(a, aset! { x: v0 });
        assert_eq!(ct, ReceiverTree::new(str!("x")));
    }

    #[test]
    fn test_app() {
        let ex = Expr::App(Box::new(Expr::Var(str!("f"))), vec![Expr::Var(str!("x"))]);

        let mut tf = TyVarFactory::new("v");
        let mono_tys = HashSet::new();
        let (t, a, ct) = ex.collect_constraints(&mono_tys, &mut tf);

        assert_eq!(t, Ty::Var(tvar!(v2)));
        assert_eq!(a, aset! { f:v0, x: v1 });
        assert_eq!(
            ct,
            AttachTree::new(
                Constraint::new(EqConstraint(
                    Ty::Var(tvar!(v0)),
                    Ty::Func(vec![Ty::Var(tvar!(v1))], Box::new(Ty::Var(tvar!(v2))))
                )),
                NodeTree::new(vec![
                    ReceiverTree::new(str!("f")),
                    ReceiverTree::new(str!("x")),
                ])
            )
        );
    }

    #[test]
    fn test_let() {
        let ex = Expr::Let(
            str!("x"),
            Box::new(Expr::Lit(LitKind::Int)),
            Box::new(Expr::Var(str!("x"))),
        );

        let mut tf = TyVarFactory::new("v");
        let mono_tys = HashSet::new();
        let (t, a, ct) = ex.collect_constraints(&mono_tys, &mut tf);

        println!("type = {}", t);
        println!("aset = {:?}", a);
        println!("ct = {:#?}", ct);
        assert_eq!(
            ct,
            AttachTree::new(
                EqConstraint::new(Ty::Var(tvar!(v4)), Ty::Var(tvar!(v2))),
                StrictTree::new(
                    AttachTree::new(
                        EqConstraint::new(Ty::Var(tvar!(v0)), Ty::Var(tvar!(v1))),
                        NodeTree::new(vec![
                            ReceiverTree::new(str!("x")),
                            AttachTree::new(
                                EqConstraint::new(Ty::Var(tvar!(v1)), Ty::int()),
                                ConstraintTree::empty()
                            )
                        ])
                    ),
                    StrictTree::new(
                        AttachTree::new(
                            GenConstraint::new(vec![], tvar!(v3), Ty::Var(tvar!(v0))),
                            ConstraintTree::empty()
                        ),
                        StrictSpreadTree::new(
                            str!("x"),
                            InstConstraint::new(Ty::Var(tvar!(v2)), Ty::Var(tvar!(v3))),
                            ReceiverTree::new(str!("x"))
                        )
                    )
                )
            )
        );
    }
}
