use std::collections::HashSet;

use crate::{
    ast::{asm::AsmOperand, HasSource, Literal, Module, Node, Path, SourceInfo},
    span::{Source, Span},
    typing::{
        assumptions::AssumptionSet,
        binding::{BindingGroup, BindingGroupAnalysis},
        collect::{CollectConstraints, CollectDeclarations, CollectPatterns},
        constraints::{
            tree::{
                AttachTree, ConstraintTree, NodeTree, ParentAttachTree, ReceiverTree,
                StrictSpreadTree,
            },
            EqConstraint, InstConstraint, ProveConstraint, SkolConstraint,
        },
        info::TypeInfo,
        predicate::TyPredicate,
        state::{TyEnv, TyVarFactory},
        traits::{HasFreeVars, HasType},
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
            HirDecl::Extern(id, ty, is_mutable, ty_src) => {
                // B = (∅,∅,•) Σ = [x1 :σ,...,xn :σ]
                let mut env = TyEnv::new();
                env.insert(id.clone(), ty.clone());
                (
                    HirDecl::Extern(id, ty.clone(), is_mutable, ty_src),
                    ty,
                    BindingGroup::empty().with_src(src.clone()),
                    env,
                )
            }
            HirDecl::Type(id, ty, is_mutable, ty_src) => {
                // B = (∅,∅,•) Σ = [x1 :σ,...,xn :σ]
                let mut env = TyEnv::new();
                env.insert(id.clone(), ty.clone());
                (
                    HirDecl::Type(id, ty.clone(), is_mutable, ty_src),
                    ty,
                    BindingGroup::empty().with_src(src.clone()),
                    env,
                )
            }
            HirDecl::Fn(name, mut params, body, decs) => {
                // ⟨M⟩, id, A\dom(E),Cl ◃◦•[ TC1,TC2 •] ⊢fb lhs = rhs : {|τ1,...,τn,τ|}
                let fn_tv = tf.next();

                // LHS
                let mut mono_tys = mono_tys.clone();
                let mut param_tys = vec![];
                let mut param_cts = vec![];
                let mut lhs_env = TyEnv::new();
                for param in params.iter_mut() {
                    let (param_ty, param_env, param_ct) = param.get_name().collect_patterns(tf);
                    if param.get_ty().is_none() {
                        param.set_ty(param_ty.clone());
                    }

                    if let Ty::Var(tv) = &param_ty {
                        mono_tys.insert(tv.clone());
                    }
                    param_tys.push(param_ty);
                    param_cts.push(param_ct);
                    lhs_env.extend(param_env);
                }

                // RHS
                // ⟨M + ftv(Cl)⟩,A,TC2 ⊢rhs rhs : τ
                let (body, aset, body_ct) = body.collect_constraints(&mono_tys, tf);

                let fn_ty = Ty::Func(param_tys, Box::new(body.ty()));

                let params_ct = NodeTree::new(param_cts);
                let cl = EqConstraint::lift(&aset, &lhs_env)
                    .into_iter()
                    .map(|(l, c)| (l, c.with_src(src.clone())))
                    .collect();

                let ct = NodeTree::new(vec![
                    ReceiverTree::new(fn_tv.to_string()),
                    ParentAttachTree::new(
                        EqConstraint::new(Ty::Var(fn_tv.clone()), fn_ty),
                        NodeTree::new(vec![params_ct, body_ct]).spread_list(cl),
                    ),
                ]);

                let mut env = TyEnv::new();
                env.insert(name.clone(), Ty::Var(fn_tv.clone()));
                let bg = BindingGroup::new(env, aset - lhs_env.keys(), ct).with_src(src.clone());
                (
                    HirDecl::Fn(name, params, body, decs),
                    Ty::Var(fn_tv),
                    bg,
                    TyEnv::new(),
                )
            }
            HirDecl::TraitMember(id, ty) => {
                // B = (∅,∅,•) Σ = [x1 :σ,...,xn :σ]
                let mut env = TyEnv::new();
                env.insert(id.clone(), ty.clone());
                (
                    HirDecl::TraitMember(id, ty.clone()),
                    ty,
                    BindingGroup::empty().with_src(src.clone()),
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
        let mut stmts = self.stmts;
        let filepath = self.filepaths[0].clone();

        let mut span = Span::new();
        if let Some(first) = stmts.first() {
            if let Some(s) = first.src().span {
                span.start = s.start;
            }
        }

        if let Some(last) = stmts.last() {
            if let Some(s) = last.src().span {
                span.end = s.end;
            }
        }

        stmts.push(Node::new(
            HirNode::Literal(Literal::Unit),
            SourceInfo::new(Source {
                filepath: filepath.clone(),
                span: None,
            }),
        ));

        let body = Node::new(
            HirNode::Block(stmts),
            SourceInfo::new(Source {
                filepath: filepath.clone(),
                span: Some(span),
            }),
        );

        // create a main function for the stmts
        let main_decl = Node::new(
            HirDecl::Fn(Path::from("main"), vec![], Box::new(body), None),
            SourceInfo::new(Source {
                filepath: filepath.clone(),
                span: Some(span),
            }),
        );

        log::debug!("{}", main_decl.value);

        let decls = std::iter::once(main_decl).chain(self.decls).into_iter();
        let mut bgroups = vec![];
        let mut sigs = TyEnv::new();
        for (decl, bg, decl_env) in decls.map(|d| d.collect_decls(mono_tys, tf)) {
            module.decls.push(decl);
            bgroups.push(bg);
            sigs.extend(decl_env);
        }

        let mono_tys = HashSet::new();
        let mut bga = BindingGroupAnalysis::new(bgroups, &sigs, tf, &mono_tys);
        let (_, aset, ct) = bga.analyze();
        log::debug!("module aset: {:?}", aset);
        let cl = InstConstraint::lift(&aset, &sigs);
        log::debug!("inst constraints: {:?}", cl);
        let ct = ct.strict_spread_list(cl);
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
            HirNode::Tuple(els) => {
                let mut aset = AssumptionSet::new();
                let mut cts = vec![];
                let mut tys = vec![];
                let mut typed_els = vec![];
                for el in els.into_iter() {
                    let (el, a, ct) = el.collect_constraints(mono_tys, tf);
                    let el_ty = el.ty();
                    tys.push(el_ty);
                    typed_els.push(el);
                    aset.extend(a);
                    cts.push(ct);
                }
                let t = Ty::Var(tf.with_scope(&src.path));
                let c = EqConstraint::new(t.clone(), Ty::Tuple(tys));
                let ct = AttachTree::new(c, NodeTree::new(cts));
                (HirNode::Tuple(typed_els), t, aset, ct)
            }
            HirNode::List(items) => {
                let ty = Ty::Var(tf.with_scope(&src.path));
                let el_ty = Ty::Var(tf.with_scope(&src.path));
                let mut aset = AssumptionSet::new();
                let mut cts = vec![];
                let mut typed_items = vec![];
                for item in items {
                    let (item, item_aset, item_ct) = item.collect_constraints(mono_tys, tf);
                    let c = EqConstraint::new(el_ty.clone(), item.ty()).with_src(src.clone());
                    cts.push(ParentAttachTree::new(c, item_ct));
                    aset.extend(item_aset);
                    typed_items.push(item);
                }

                let c = EqConstraint::new(ty.clone(), Ty::list(el_ty));
                let ct = AttachTree::new(c, NodeTree::new(cts));
                (HirNode::List(typed_items), ty, aset, ct)
            }
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
            HirNode::Range(start, end, is_inclusive) => {
                let (start, start_aset, start_ct) = start.collect_constraints(mono_tys, tf);
                let (end, end_aset, end_ct) = end.collect_constraints(mono_tys, tf);
                let ty = Ty::Var(tf.with_scope(&src.path));
                let el_ty = Ty::Var(tf.with_scope(&src.path));
                let ct = AttachTree::new(
                    EqConstraint::new(ty.clone(), Ty::range(el_ty.clone())).with_src(src.clone()),
                    NodeTree::new(vec![
                        ParentAttachTree::new(
                            EqConstraint::new(el_ty.clone(), start.ty()).with_src(src.clone()),
                            start_ct,
                        ),
                        ParentAttachTree::new(
                            EqConstraint::new(el_ty.clone(), end.ty()).with_src(src.clone()),
                            end_ct,
                        ),
                    ]),
                );

                let mut aset = AssumptionSet::new();
                aset.extend(start_aset);
                aset.extend(end_aset);

                (HirNode::Range(start, end, is_inclusive), ty, aset, ct)
            }
            HirNode::Asm(ty, inst) => {
                let mut aset = AssumptionSet::new();
                let mut cts = vec![];
                let inst = inst
                    .into_iter()
                    .map(|(op, rands)| {
                        for v in rands.iter() {
                            let t = Ty::Var(tf.with_scope(&src.path));
                            match v {
                                AsmOperand::Var(v) => {
                                    let label = t.to_string();
                                    aset.add(Path::from(v.as_str()), t.clone());
                                    cts.push(ReceiverTree::new(label));
                                }
                                AsmOperand::Int(_) => continue,
                            }
                        }
                        (op, rands)
                    })
                    .collect::<Vec<_>>();

                let last_ty = inst.last().map(|(op, _)| op.ret_ty()).unwrap_or_default();
                let v = Ty::Var(tf.with_scope(&src.path));
                let mut cs = vec![];
                if let Some(ty) = &ty {
                    cs.push(EqConstraint::new(ty.clone(), v.clone()).with_src(src.clone()));
                }

                cs.push(EqConstraint::new(last_ty, v.clone()).with_src(src.clone()));
                cts.push(ConstraintTree::list(cs, ConstraintTree::empty()));

                let mut ct = ConstraintTree::empty();
                for t in cts.into_iter().rev() {
                    let nodes = if ct.is_empty() { vec![t] } else { vec![t, ct] };
                    ct = NodeTree::new(nodes);
                }

                (HirNode::Asm(Some(v.clone()), inst), v, aset, ct)
            }
            HirNode::Cast(e, to_ty) => {
                let src = e.info.clone();
                let (from, a, ct) = e.collect_constraints(mono_tys, tf);
                let v = Ty::Var(tf.with_scope(&src.path));
                // TODO: should there be a cast constraint?
                let c = EqConstraint::new(v.clone(), to_ty.clone()).with_src(src);
                (from.value, v, a, AttachTree::new(c, ct))
            }
            HirNode::Struct(fqn, ty, fields) => {
                let v = Ty::Var(tf.with_scope(&src.path));
                let c1 = InstConstraint::new(v.clone(), ty.clone()).with_src(src.clone());
                let mut cts = vec![AttachTree::new(c1, ConstraintTree::empty())];
                let mut typed_fields = vec![];
                let mut field_tys = vec![];
                let mut aset = AssumptionSet::new();
                for (fname, fnode) in fields {
                    let (typed_field, a, ct) = fnode.collect_constraints(mono_tys, tf);
                    aset.extend(a);
                    cts.push(AttachTree::new(
                        ProveConstraint::new(TyPredicate::HasMember(
                            v.clone(),
                            fname.clone(),
                            // typed_field.ty()
                        ))
                        .with_src(src.clone()),
                        ct,
                    ));
                    field_tys.push(typed_field.ty());
                    typed_fields.push((fname, typed_field));
                }

                let ty_args = (0..ty.get_ty_params().len())
                    .into_iter()
                    .map(|_| Ty::Var(tf.with_scope(&src.path)))
                    .collect();

                let c2 = EqConstraint::new(
                    v.clone(),
                    Ty::Projection(fqn.to_string(), ty_args, field_tys),
                )
                .with_src(src.clone());
                log::debug!("c2 = {:?}", c2);

                let ct = AttachTree::new(c2, NodeTree::new(cts));

                (HirNode::Struct(fqn, ty, typed_fields), v, aset, ct)
            }
            HirNode::Decl(_) => todo!(),
            HirNode::DerefAssign(lhs, rhs) => {
                let (lhs, lhs_aset, lhs_ct) = lhs.collect_constraints(mono_tys, tf);
                let (rhs, rhs_aset, rhs_ct) = rhs.collect_constraints(mono_tys, tf);
                let mut aset = AssumptionSet::new();
                aset.extend(lhs_aset);
                aset.extend(rhs_aset);
                let el_ty = Ty::Var(tf.with_scope(&src.path));
                let ct = NodeTree::new(vec![
                    ParentAttachTree::new(
                        EqConstraint::new(Ty::ptr(el_ty.clone()), lhs.ty()).with_src(src.clone()),
                        lhs_ct,
                    ),
                    ParentAttachTree::new(
                        EqConstraint::new(el_ty.clone(), rhs.ty()).with_src(src.clone()),
                        rhs_ct,
                    ),
                ]);
                (HirNode::DerefAssign(lhs, rhs), Ty::unit(), aset, ct)
            }
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
            HirNode::Fn(mut params, body, decs) => {
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
                    env.insert(Path::from(name), ty);
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
                    HirNode::Fn(params, body, decs),
                    fun_ty,
                    aset - env.keys(),
                    AttachTree::new(c, ct),
                )
            }
            HirNode::Dot(lhs, member) => {
                let (lhs, aset, ct) = lhs.collect_constraints(mono_tys, tf);
                let member_ty = Ty::Var(tf.with_scope(&src.path));
                let c = ProveConstraint::new(TyPredicate::HasMember(
                    lhs.ty(),
                    member.name().clone(),
                    // member_ty.clone(),
                ))
                .with_src(src.clone());

                let member = Node {
                    id: member.id,
                    value: member.value,
                    info: HirInfo {
                        src_info: member.info,
                        ty_info: TypeInfo::new(member_ty.clone()),
                    },
                };
                (
                    HirNode::Dot(lhs, member),
                    member_ty,
                    aset,
                    AttachTree::new(c, ct),
                )
            }
            HirNode::Apply(fun, args) => {
                let mut aset = AssumptionSet::new();
                let mut typed_args = vec![];
                let mut arg_tys = vec![];
                let mut arg_cts = vec![];

                let (fun, ct1) = if let HirNode::Dot(self_arg, field) = fun.value {
                    let (self_arg, self_aset, ct1) = self_arg.collect_constraints(mono_tys, tf);
                    let src_info = self_arg.info.src_info.clone();
                    let self_ty = self_arg.ty();
                    arg_tys.push(self_ty.clone());
                    aset.extend(self_aset);
                    typed_args.push(*self_arg);
                    let fqn = Path::from(format!(
                        "{}::{}",
                        self_ty.clone().get_path().unwrap(),
                        field.name()
                    ));
                    let member_ty = Ty::Var(tf.with_scope(&src.path));
                    (
                        Box::new(Node {
                            id,
                            value: HirNode::Var(fqn),
                            info: HirInfo {
                                src_info,
                                ty_info: TypeInfo::new(member_ty),
                            },
                        }),
                        ct1,
                    )
                } else {
                    let (fun, fun_aset, ct1) = fun.collect_constraints(mono_tys, tf);
                    aset.extend(fun_aset);
                    (fun, ct1)
                };

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
                let anno_ty = n.ty();
                let (id, n, hir_info) = n.unpack();
                let src_info = hir_info.src_info;
                let n = Node {
                    id,
                    value: n,
                    info: src_info,
                };
                let (n, aset, ctree) = n.collect_constraints(mono_tys, tf);
                let c1 = SkolConstraint::new(mono_tys.clone(), n.ty(), anno_ty.clone())
                    .with_src(src.clone());
                let b = Ty::Var(tf.with_scope(&src.path));
                let c2 = InstConstraint::new(b.clone(), anno_ty.clone()).with_src(src.clone());
                (
                    n.value,
                    anno_ty,
                    aset,
                    AttachTree::new(c2, NodeTree::new(vec![ParentAttachTree::new(c1, ctree)])),
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
