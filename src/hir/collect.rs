use std::collections::HashSet;

use crate::{
    ast::{Literal, Module, Node, SourceInfo},
    span::Source,
    typing::{
        assumptions::AssumptionSet,
        binding::{BindingGroup, BindingGroupAnalysis},
        collect::{CollectConstraints, CollectDeclarations, CollectPatterns},
        constraints::{
            tree::{AttachTree, ConstraintTree, NodeTree, ReceiverTree, StrictSpreadTree},
            EqConstraint, ProveConstraint,
        },
        info::TypeInfo,
        predicate::TyPredicate,
        state::{TyEnv, TyVarFactory},
        traits::HasType,
        ty::{LiteralKind, Ty, TyVar},
    },
};

use super::{HirDecl, HirInfo, HirNode, HirPattern};

impl CollectPatterns for HirPattern {
    fn collect_patterns(&self, tf: &mut TyVarFactory) -> (Ty, TyEnv, ConstraintTree) {
        match self {
            HirPattern::Var(var) => var.collect_patterns(tf),
        }
    }
}

impl CollectDeclarations for Node<HirDecl<SourceInfo>, SourceInfo> {
    type Output = Node<HirDecl<HirInfo>, HirInfo>;

    fn collect_decls(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self::Output, BindingGroup, TyEnv) {
        let id = self.id;
        let src = self.info;
        let (value, ty, bg, env) = match self.value {
            HirDecl::Pattern(var, rhs) => {
                let ((var, rhs, src), bg, env) =
                    (var, rhs, src.clone()).collect_decls(mono_tys, tf);
                let ty = rhs.ty();
                (HirDecl::Pattern(var, rhs), ty, bg, env)
            }
            HirDecl::Type(id, ty) => {
                // B = (∅,∅,•) Σ = [x1 :σ,...,xn :σ]
                let mut env = TyEnv::new();
                env.insert(id.clone(), ty.clone());
                (
                    HirDecl::Type(id, ty.clone()),
                    ty,
                    BindingGroup::new(TyEnv::new(), AssumptionSet::new(), ConstraintTree::empty())
                        .with_src(src.clone()),
                    env,
                )
            }
        };

        (
            Node {
                id,
                value,
                info: HirInfo {
                    src_info: src,
                    ty_info: TypeInfo::new(ty),
                },
            },
            bg,
            env,
        )
    }
}

impl CollectConstraints for Module<HirNode<SourceInfo>, HirDecl<SourceInfo>, SourceInfo> {
    type Output = Module<HirNode<HirInfo>, HirDecl<HirInfo>, HirInfo>;

    fn collect_constraints(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let mut module = Module::new_from(&self);
        let mut nodes = self.stmts;
        let decls = self.decls;
        let filepath = self.filepaths[0].clone();

        let body = if nodes.len() == 1 {
            nodes.pop().unwrap()
        } else {
            Node::new(
                HirNode::Block(nodes),
                SourceInfo::new(Source {
                    filepath: filepath.clone(),
                    span: None,
                }),
            )
        };

        let node = if decls.len() == 0 {
            body
        } else {
            Node::new(
                HirNode::Let(decls, Box::new(body)),
                SourceInfo::new(Source {
                    filepath,
                    span: None,
                }),
            )
        };

        let (node, aset, ct) = node.collect_constraints(mono_tys, tf);
        module.stmts.push(node);
        (module, aset, ct)
    }
}

impl CollectConstraints for Node<HirNode<SourceInfo>, SourceInfo> {
    type Output = Node<HirNode<HirInfo>, HirInfo>;

    fn collect_constraints(
        self,
        mono_tys: &HashSet<TyVar>,
        tf: &mut TyVarFactory,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let (id, value, src) = self.unpack();
        let (value, ty, aset, ct) = match value {
            HirNode::Block(stmts) => {
                let mut ty = Ty::unit();
                let mut aset = AssumptionSet::new();
                let mut cts = vec![];
                let mut typed_stmts = vec![];
                for stmt in stmts.into_iter() {
                    let (stmt, a, ct) = stmt.collect_constraints(mono_tys, tf);
                    let stmt_ty = stmt.ty();
                    let b = Ty::Var(tf.with_scope(&src.path));
                    let c =
                        EqConstraint::new(b.clone(), stmt_ty).with_src(stmt.info.src_info.clone());
                    typed_stmts.push(stmt);
                    ty = b;
                    aset.extend(a);
                    cts.push(AttachTree::new(c, ct));
                }
                let mut ct = ConstraintTree::empty();
                for t in cts.into_iter().rev() {
                    let nodes = if ct.is_empty() { vec![t] } else { vec![t, ct] };
                    ct = NodeTree::new(nodes);
                }

                (HirNode::Block(typed_stmts), ty, aset, ct)
            }
            HirNode::Var(v) => {
                let t = Ty::Var(tf.with_scope(&src.path));
                let label = t.to_string();
                let mut aset = AssumptionSet::new();
                aset.add(v.clone(), t.clone());
                (HirNode::Var(v), t, aset, ReceiverTree::new(label))
            }
            HirNode::Type(t) => (
                HirNode::Type(t.clone()),
                t.clone(),
                AssumptionSet::new(),
                ConstraintTree::empty(),
            ),
            HirNode::Literal(lit) => {
                let mut ctree = ConstraintTree::empty();
                let t = match &lit {
                    Literal::Integer { size, signed, .. } => {
                        if *size != 0 {
                            let sign = if !signed { "u" } else { "i" };
                            Ty::con(format!("{}{}", sign, size))
                        } else {
                            let t = Ty::Var(tf.with_scope(&src.path));
                            ctree = ConstraintTree::list(
                                vec![ProveConstraint::new(TyPredicate::Trait(Ty::Projection(
                                    str!("core::Int"),
                                    vec![t.clone()],
                                    vec![],
                                )))
                                .with_src(src.clone())],
                                ctree,
                            );
                            t
                        }
                    }
                    Literal::Float { size, .. } => {
                        if *size != 0 {
                            Ty::con(format!("f{}", size))
                        } else {
                            let t = Ty::Var(tf.with_scope(&src.path));
                            ctree = ConstraintTree::list(
                                vec![ProveConstraint::new(TyPredicate::Literal(
                                    t.clone(),
                                    LiteralKind::Float,
                                ))
                                .with_src(src.clone())],
                                ctree,
                            );
                            t
                        }
                    }
                    Literal::String(_) => Ty::string(),
                    Literal::ByteString(_) => Ty::bytes(),
                    Literal::Byte(_) => Ty::u8(),
                    Literal::Char(_) => Ty::char(),
                    Literal::Bool(_) => Ty::bool(),
                    Literal::Nil => Ty::nil(),
                    Literal::Unit => Ty::unit(),
                    Literal::UnicodeEscSeq(_) => unimplemented!("unicode escape sequence"),
                };

                let v = Ty::Var(tf.with_scope(&src.path));
                let c = EqConstraint::new(v.clone(), t.clone()).with_src(src.clone());
                (
                    HirNode::Literal(lit),
                    v,
                    AssumptionSet::new(),
                    AttachTree::new(c, ctree),
                )
            }
            HirNode::Cast(e, to_ty) => {
                let src = e.info.clone();
                let (from, a, ct) = e.collect_constraints(mono_tys, tf);
                let v = Ty::Var(tf.with_scope(&src.path));
                let cast_ty = Ty::Cast(Box::new(from.ty()), Box::new(to_ty.clone()));
                let c = EqConstraint::new(v.clone(), cast_ty).with_src(src);
                (HirNode::Cast(from, to_ty), v, a, AttachTree::new(c, ct))
            }
            HirNode::Struct(_, _) => todo!(),
            HirNode::Decl(_) => todo!(),
            HirNode::Let(decls, body) => {
                let mut typed_decls = vec![];
                let mut decl_bgs = vec![];
                let mut envs = vec![];
                for d in decls {
                    let (d, b, e) = d.collect_decls(mono_tys, tf);
                    typed_decls.push(d);
                    decl_bgs.push(b);
                    envs.push(e);
                }

                let (body, aset, ctree) = body.collect_constraints(mono_tys, tf);
                let mut groups =
                    vec![BindingGroup::new(TyEnv::new(), aset, ctree).with_src(src.clone())];
                groups.extend(decl_bgs);

                let env = envs.into_iter().fold(TyEnv::new(), |mut acc, e| {
                    acc.extend(e);
                    acc
                });

                let mut bga = BindingGroupAnalysis::new(groups, &env, tf, mono_tys);
                let (_, a, t) = bga.analyze();

                let b = Ty::Var(tf.with_scope(&src.path));
                let c = EqConstraint::new(b.clone(), body.ty()).with_src(src.clone());
                (HirNode::Let(typed_decls, body), b, a, AttachTree::new(c, t))
            }
            HirNode::Fun(mut params, body) => {
                let mut mono_tys = mono_tys.clone();
                let mut param_tys = vec![];
                let mut env = TyEnv::new();
                let mut cts = vec![];
                for p in params.iter_mut() {
                    let tv = tf.with_scope(&src.path);
                    mono_tys.insert(tv.clone());
                    let ty = Ty::Var(tv.clone());
                    if p.get_ty().is_none() {
                        p.set_ty(ty.clone());
                    }

                    let name = p.get_name().clone();
                    cts.push(ReceiverTree::new(tv.to_string()));
                    param_tys.push(ty.clone());
                    env.insert(name, ty);
                }

                let (body, aset, ct) = body.collect_constraints(&mono_tys, tf);
                cts.push(ct);

                let cl = EqConstraint::lift(&aset, &env)
                    .into_iter()
                    .map(|(s, c)| (s, c.with_src(src.clone())));
                let ct = cl.into_iter().rfold(NodeTree::new(cts), |ct, (x, c)| {
                    StrictSpreadTree::new(x, c, ct)
                });

                let fun_ty = Ty::Var(tf.with_scope(&src.path));
                let c = EqConstraint::new(fun_ty.clone(), Ty::Func(param_tys, Box::new(body.ty())))
                    .with_src(src.clone());

                (
                    HirNode::Fun(params, body),
                    fun_ty,
                    aset - env.keys(),
                    AttachTree::new(c, ct),
                )
            }
            HirNode::Apply(fun, args) => {
                let mut aset = AssumptionSet::new();
                let mut arg_tys = vec![];
                let mut arg_cts = vec![];

                let (fun, fun_aset, ct1) = fun.collect_constraints(mono_tys, tf);
                aset.extend(fun_aset);

                let mut typed_args = vec![];
                for (arg, a, ct) in args
                    .into_iter()
                    .map(|a| a.collect_constraints(mono_tys, tf))
                {
                    aset.extend(a);
                    arg_tys.push(arg.ty());
                    arg_cts.push(ct);
                    typed_args.push(arg);
                }

                let ret_ty = Ty::Var(tf.with_scope(&src.path));
                let c = EqConstraint::new(fun.ty(), Ty::Func(arg_tys, Box::new(ret_ty.clone())))
                    .with_src(src.clone());

                let mut cts = vec![ct1];
                cts.extend(arg_cts);

                (
                    HirNode::Apply(fun, typed_args),
                    ret_ty,
                    aset,
                    AttachTree::new(c, NodeTree::new(cts)),
                )
            }
            HirNode::Typed(n) => {
                todo!("{}", n)
                // let (ex, prev_ty) = n.
                // let (n, aset, ctree) = ex.collect_constraints(mono_tys, tf);
                // let c1 = SkolConstraint::new(mono_tys.clone(), n.ty(), prev_ty.clone())
                //     .with_src(src.clone());
                // let b = Ty::Var(tf.with_scope(&src.path));
                // let c2 = InstConstraint::new(b.clone(), prev_ty).with_src(src.clone());
                // (
                //     n.kind,
                //     b,
                //     aset,
                //     AttachTree::new(c2, NodeTree::new(vec![ParentAttachTree::new(c1, ctree)])),
                // )
            }
        };

        log::debug!("aset = {:#?}", aset);

        (
            Node {
                id,
                value,
                info: HirInfo {
                    src_info: src,
                    ty_info: TypeInfo::new(ty),
                },
            },
            aset,
            ct,
        )
    }
}

// #[cfg(test)]
// mod hir_collect_tests {
//     use std::collections::HashSet;

//     use crate::{
//         ast::Literal,
//         hir::{HirDecl, HirNode::*},
//         tvar,
//         typing::{
//             collect::CollectConstraints,
//             constraints::{
//                 tree::{
//                     AttachTree, ConstraintTree, NodeTree, ReceiverTree, StrictSpreadTree,
//                     StrictTree,
//                 },
//                 EqConstraint, GenConstraint, InstConstraint,
//             },
//             state::TyVarFactory,
//             ty::Ty,
//         },
//     };

//     #[test]
//     fn test_collect() {
//         let ex: HirNode = Let(
//             vec![HirDecl::var("x", Literal(Literal::new_int(10)))],
//             Box::new(Var(str!("x")).into()),
//         )
//         .into();

//         let mut tf = TyVarFactory::new("v");
//         let mono_tys = HashSet::new();
//         let (t, a, ct) = ex.collect_constraints(&mono_tys, &mut tf);

//         println!("type = {}", t);
//         println!("aset = {:?}", a);
//         println!("ct = {:#?}", ct);
//         assert_eq!(
//             ct,
//             AttachTree::new(
//                 EqConstraint::new(Ty::Var(tvar!(v4)), Ty::Var(tvar!(v2))),
//                 StrictTree::new(
//                     AttachTree::new(
//                         EqConstraint::new(Ty::Var(tvar!(v0)), Ty::Var(tvar!(v1))),
//                         NodeTree::new(vec![
//                             ReceiverTree::new(str!("x")),
//                             AttachTree::new(
//                                 EqConstraint::new(Ty::Var(tvar!(v1)), Ty::int()),
//                                 ConstraintTree::empty()
//                             )
//                         ])
//                     ),
//                     StrictTree::new(
//                         AttachTree::new(
//                             GenConstraint::new(vec![], tvar!(v3), Ty::Var(tvar!(v0))),
//                             ConstraintTree::empty()
//                         ),
//                         StrictSpreadTree::new(
//                             str!("x"),
//                             InstConstraint::new(Ty::Var(tvar!(v2)), Ty::Var(tvar!(v3))),
//                             ReceiverTree::new(str!("x"))
//                         )
//                     )
//                 )
//             )
//         );
//     }
// }
