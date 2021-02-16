use std::{collections::HashSet, ops::Deref};

use ast::{Extern, Module, Sequence};

use crate::{
    ast,
    hir::HirInfo,
    span::{Source, SourceMap, Span},
    typing::{
        assumptions::AssumptionSet,
        binding::{BindingGroup, BindingGroupAnalysis},
        collect::{CollectConstraints, CollectDeclarations, CollectPatterns},
        constraints::{
            tree::{AttachTree, ConstraintTree, NodeTree, ParentAttachTree, ReceiverTree},
            EqConstraint, InstConstraint, ProveConstraint, SkolConstraint,
        },
        info::TypeInfo,
        predicate::TyPredicate,
        state::{TyEnv, TyVarFactory},
        traits::HasType,
        ty::{LiteralKind, Ty, TyVar},
        TyCtx,
    },
};

use super::{
    asm::{Asm, AsmOperand},
    Assign, BinOp, Block, Call, Cast, Curly, CurlyElement, Decl, Dot, Expr, For, If, List, Literal,
    Name, Node, Path, Pattern, Range, Tuple, While,
};

impl CollectPatterns for Node<Pattern> {
    fn collect_patterns(&self, srcmap: &SourceMap, tcx: &mut TyCtx) -> (Ty, TyEnv, ConstraintTree) {
        match &self.value {
            Pattern::Name(n) => n.path.collect_patterns(srcmap, tcx),
            Pattern::Sequence(_) => todo!("collect patterns: {}", self),
            Pattern::Tuple(_) => todo!("collect patterns: {}", self),
        }
    }
}

impl CollectDeclarations for Node<Decl> {
    fn collect_decls(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (BindingGroup, TyEnv) {
        let src = srcmap.get(self);
        let (ty, bg, env) = match &self.value {
            Decl::Extern(ext) => {
                // B = (∅,∅,•) Σ = [x1 :σ,...,xn :σ]
                let mut env = TyEnv::new();
                let (fqn, ty) = match ext.decl() {
                    Decl::Mutable(n) => {
                        let ty = n.ty.as_deref().unwrap().clone();
                        let fqn = n.path.clone();
                        (fqn, ty)
                    }
                    Decl::Name(n) => {
                        let ty = n.ty.as_deref().unwrap().clone();
                        let fqn = n.path.clone();
                        (fqn, ty)
                    }
                    Decl::FnSig(sig) => {
                        let fqn = sig.path.clone();
                        let ty = sig.ty.as_ref().unwrap().clone();
                        (fqn, ty)
                    }
                    d @ _ => unreachable!("Decl::Extern: {:?}", d),
                };

                env.insert(fqn, ty.clone());

                (ty, BindingGroup::empty().with_src(src.clone()), env)
            }
            Decl::Fn(func) => {
                // name, mut params, body, decs
                let name = &func.sig.path;

                // ⟨M⟩, id, A\dom(E),Cl ◃◦•[ TC1,TC2 •] ⊢fb lhs = rhs : {|τ1,...,τn,τ|}
                let fn_tv = tcx.tf().next();

                // LHS
                let mut mono_tys = mono_tys.clone();
                let mut param_tys = vec![];
                let mut param_cts = vec![];
                let mut lhs_env = TyEnv::new();
                for param in func.sig.params.iter() {
                    let (param_ty, param_env, param_ct) =
                        param.name().unwrap().collect_patterns(srcmap, tcx);

                    if let Ty::Var(tv) = &param_ty {
                        mono_tys.insert(tv.clone());
                    }
                    param_tys.push(param_ty.clone());
                    param_cts.push(param_ct);
                    lhs_env.extend(param_env);
                    tcx.set_ty(&param, param_ty);
                }

                // RHS
                // ⟨M + ftv(Cl)⟩,A,TC2 ⊢rhs rhs : τ
                let (body_ty, aset, body_ct) = func
                    .body
                    .as_deref()
                    .unwrap()
                    .collect_constraints(&mono_tys, srcmap, tcx);

                let fn_ty = Ty::Func(param_tys, Box::new(body_ty));

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

                let mut env = TyEnv::new();
                if let Some(ty) = &func.sig.ty {
                    log::debug!("type of {}: {}", name, ty);
                    env.insert(name.clone(), ty.clone());
                }
                (Ty::Var(fn_tv), bg, env)
            }
            Decl::Mutable(d) => todo!("collect_decls: Decl::Mutable: {:?}", d),
            Decl::Name(d) => todo!("collect_decls: Decl::Name: {:?}", d),
            Decl::Declare(d) => todo!("collect_decls: Decl::Declare: {:?}", d),
            Decl::FnSig(d) => todo!("collect_decls: Decl::FnSig: {:?}", d),
            Decl::Struct(st) => (
                Ty::unit(),
                BindingGroup::empty().with_src(src.clone()),
                TyEnv::new(),
            ),
            Decl::Trait(tr) => {
                let mut env = TyEnv::new();
                for func in tr.funcs.iter() {
                    env.insert(func.path.clone(), func.ty.clone().unwrap());
                }
                (Ty::unit(), BindingGroup::empty().with_src(src.clone()), env)
            }
            Decl::TypeAlias(d, _) => todo!("collect_decls: Decl::TypeAlias: {:?}", d),
            Decl::Impl(imp) => {
                let mut env = TyEnv::new();
                let mut bg = BindingGroup::empty().with_src(src.clone());
                if let Some(funcs) = &imp.funcs {
                    for func in funcs {
                        let (fn_bg, fn_env) = func.collect_decls(mono_tys, srcmap, tcx);
                        bg.combine(fn_bg);
                        env.extend(fn_env);
                    }
                }

                if let Some(ext) = &imp.externs {
                    for e in ext {
                        let (ext_bg, ext_env) = e.collect_decls(mono_tys, srcmap, tcx);
                        bg.combine(ext_bg);
                        env.extend(ext_env);
                    }
                }

                (Ty::unit(), bg, env)
            }
        };

        tcx.set_ty(&self, ty);
        (bg, env)
    }
}

impl<'a> CollectConstraints for Module<Expr, Decl> {
    type Output = ();

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let mut bgroups = vec![];
        let mut sigs = TyEnv::new();
        for (bg, decl_env) in self
            .decls
            .iter()
            .map(|d| d.collect_decls(mono_tys, srcmap, tcx))
        {
            bgroups.push(bg);
            sigs.extend(decl_env);
        }

        let mono_tys = HashSet::new();
        let mut bga = BindingGroupAnalysis::new(bgroups, &sigs, tcx.tf(), &mono_tys);
        let (_, aset, ct) = bga.analyze();
        log::debug!("module aset: {:?}", aset);
        let cl = InstConstraint::lift(&aset, &sigs);
        log::debug!("inst constraints: {:?}", cl);
        let ct = ct.strict_spread_list(cl);
        ((), aset, ct)
    }
}

impl<T, U> CollectConstraints for (&Box<T>, &Source)
where
    T: CollectConstraints<Output = U>,
{
    type Output = U;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(b, src) = self;
        let (out, aset, ct) = b.collect_constraints(mono_tys, srcmap, tcx);
        (out, aset, ct)
    }
}

impl CollectConstraints for Node<Expr> {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let src = &srcmap.get(self);
        let (ty, aset, ct) = match &self.value {
            Expr::Assign(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Asm(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::BinOp(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Block(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Break(ex) => todo!(),
            Expr::Call(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Cast(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Closure(ex) => todo!(),
            Expr::Curly(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::DefaultValue(ex) => todo!(),
            Expr::Dot(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Fn(ex) => todo!(),
            Expr::For(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::If(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Index(ex) => {
                todo!()
                // (ex, src).collect_constraints(mono_tys, srcmap, tcx)
            }
            Expr::Labeled(lhs, rhs) => todo!(),
            Expr::List(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Literal(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Loop(ex) => todo!(),
            Expr::Name(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Path(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Paren(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Range(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Return(ex) => todo!(),
            Expr::Sequence(ex) => todo!(),
            Expr::Tuple(ex) => (ex, src).collect_constraints(mono_tys, srcmap, tcx),
            Expr::Type(ex) => todo!(),
            Expr::TypeAnnotated(ex, ty) => {
                let anno_ty = ty.deref().deref().clone();
                let (ty, aset, ctree) = ex.collect_constraints(mono_tys, srcmap, tcx);
                let c1 = SkolConstraint::new(mono_tys.clone(), ty, anno_ty.clone())
                    .with_src(src.clone());
                let b = Ty::Var(tcx.tf().with_scope(&src.path));
                let c2 = InstConstraint::new(b.clone(), anno_ty.clone()).with_src(src.clone());
                (
                    anno_ty,
                    aset,
                    AttachTree::new(c2, NodeTree::new(vec![ParentAttachTree::new(c1, ctree)])),
                )
            }
            Expr::UnaryOp(ex) => todo!(),
            Expr::Unsafe(ex) => todo!(),
            Expr::While(ex) => todo!(),
        };

        tcx.set_ty(self, ty.clone());
        (ty, aset, ct)
    }
}

impl CollectConstraints for (&Assign, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(assign, src) = self;
        let (bg, env) =
            (&assign.lhs, assign.rhs.as_ref(), src).collect_decls(mono_tys, srcmap, tcx);

        let lhs_ty = Ty::Var(tcx.tf().with_scope(&src.path));
        tcx.set_ty(&assign.lhs, lhs_ty);

        let groups = vec![bg];
        let mut bga = BindingGroupAnalysis::new(groups, &env, tcx.tf(), mono_tys);
        let (_, aset, ct) = bga.analyze();

        let c =
            EqConstraint::new(tcx.ty_of(&assign.lhs), tcx.ty_of(&assign.rhs)).with_src(src.clone());

        (Ty::unit(), aset, AttachTree::new(c, ct))
    }
}

impl CollectConstraints for (&Asm, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(asm, src) = self;
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];
        for (op, rands) in asm.inst.iter() {
            for v in rands.iter() {
                let t = Ty::Var(tcx.tf().with_scope(&src.path));
                match v {
                    AsmOperand::Var(v) => {
                        let label = t.to_string();
                        aset.add(Path::from(v.as_str()), t.clone());
                        cts.push(ReceiverTree::new(label));
                    }
                    AsmOperand::Int(_) => continue,
                }
            }
        }

        let last_ty = asm
            .inst
            .last()
            .map(|(op, _)| op.ret_ty())
            .unwrap_or_default();
        let v = Ty::Var(tcx.tf().with_scope(&src.path));
        let mut cs = vec![];
        if let Some(ty) = asm.ret_ty.as_deref() {
            cs.push(EqConstraint::new(ty.clone(), v.clone()).with_src(src.clone()));
        }

        cs.push(EqConstraint::new(last_ty, v.clone()).with_src(src.clone()));
        cts.push(ConstraintTree::list(cs, ConstraintTree::empty()));

        let mut ct = ConstraintTree::empty();
        for t in cts.into_iter().rev() {
            let nodes = if ct.is_empty() { vec![t] } else { vec![t, ct] };
            ct = NodeTree::new(nodes);
        }

        (v, aset, ct)
    }
}

impl CollectConstraints for (&BinOp, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        panic!("this should be desugared into a call")
    }
}

impl CollectConstraints for (&Block, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(block, src) = self;
        let mut ty = Ty::unit();
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];

        for stmt in block.stmts.iter() {
            let (stmt_ty, a, ct) = stmt.collect_constraints(mono_tys, srcmap, tcx);
            let b = Ty::Var(tcx.tf().with_scope(&src.path));
            let src = srcmap.get(stmt);
            let c = EqConstraint::new(b.clone(), stmt_ty).with_src(src);
            ty = b;
            aset.extend(a);
            cts.push(AttachTree::new(c, ct));
        }
        let mut ct = ConstraintTree::empty();
        for t in cts.into_iter().rev() {
            let nodes = if ct.is_empty() { vec![t] } else { vec![t, ct] };
            ct = NodeTree::new(nodes);
        }

        (ty, aset, ct)
    }
}

impl CollectConstraints for (&Call, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(call, src) = self;
        let mut aset = AssumptionSet::new();
        let mut arg_tys = vec![];
        let mut arg_cts = vec![];

        let (lhs_ty, ct1) = if let Expr::Dot(dot) = &call.lhs.value {
            let (self_ty, self_aset, ct1) = dot.lhs.collect_constraints(mono_tys, srcmap, tcx);
            arg_tys.push(self_ty.clone());
            aset.extend(self_aset);
            let fqn = Path::from(format!(
                "{}::{}",
                self_ty.clone().get_path().unwrap(),
                dot.rhs.path
            ));

            let src = srcmap.get(&dot.lhs);
            let member_ty = Ty::Var(tcx.tf().with_scope(&src.path));
            let node = Node {
                id: call.lhs.id,
                value: Expr::Path(fqn),
            };
            tcx.set_ty(&node, member_ty.clone());
            (member_ty, ct1)
        } else {
            let (lhs_ty, fun_aset, ct1) = call.lhs.collect_constraints(mono_tys, srcmap, tcx);
            aset.extend(fun_aset);
            (lhs_ty, ct1)
        };

        for (arg_ty, a, ct) in call
            .args
            .items
            .iter()
            .map(|a| a.collect_constraints(mono_tys, srcmap, tcx))
        {
            aset.extend(a);
            arg_tys.push(arg_ty);
            arg_cts.push(ct);
        }

        let ret_ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let c = EqConstraint::new(lhs_ty, Ty::Func(arg_tys, Box::new(ret_ty.clone())))
            .with_src(src.clone());

        let mut cts = vec![ct1];
        cts.extend(arg_cts);

        (ret_ty, aset, AttachTree::new(c, NodeTree::new(cts)))
    }
}

impl CollectConstraints for (&Cast, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(cast, src) = self;
        let (from_ty, a, ct) = cast.lhs.collect_constraints(mono_tys, srcmap, tcx);
        let v = Ty::Var(tcx.tf().with_scope(&src.path));
        // TODO: should there be a cast constraint?
        let c = EqConstraint::new(v.clone(), cast.ty.deref().clone()).with_src(src.clone());
        (v, a, AttachTree::new(c, ct))
    }
}

impl CollectConstraints for (&Curly, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(curly, src) = self;
        let v = Ty::Var(tcx.tf().with_scope(&src.path));
        let c1 = InstConstraint::new(v.clone(), curly.ty.clone()).with_src(src.clone());
        let mut cts = vec![AttachTree::new(c1, ConstraintTree::empty())];
        let mut field_tys = vec![];
        let mut aset = AssumptionSet::new();
        for el in curly.elements.iter() {
            let (name, (field_ty, a, ct)) = match &el.value {
                CurlyElement::Labeled(name, field) => {
                    (name, field.collect_constraints(mono_tys, srcmap, tcx))
                }
                _ => unreachable!("all elements should be labeled at this point"),
            };
            aset.extend(a);
            cts.push(AttachTree::new(
                ProveConstraint::new(TyPredicate::HasMember(
                    v.clone(),
                    name.path.to_string(),
                    // typed_field.ty()
                ))
                .with_src(src.clone()),
                ct,
            ));
            field_tys.push(field_ty.clone());
            tcx.set_ty(&el, field_ty);
        }

        let ty_args = (0..curly.ty.get_ty_params().len())
            .into_iter()
            .map(|_| Ty::Var(tcx.tf().with_scope(&src.path)))
            .collect();

        let fqn = curly.lhs.as_ref().unwrap().to_string();
        let c2 = EqConstraint::new(v.clone(), Ty::Projection(fqn, ty_args, field_tys))
            .with_src(src.clone());

        let ct = AttachTree::new(c2, NodeTree::new(cts));

        (v, aset, ct)
    }
}

impl CollectConstraints for (&Dot, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(dot, src) = self;
        let (lhs_ty, aset, ct) = dot.lhs.collect_constraints(mono_tys, srcmap, tcx);
        let member_ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let c = ProveConstraint::new(TyPredicate::HasMember(
            lhs_ty,
            dot.rhs.path.to_string(),
            // member_ty.clone(),
        ))
        .with_src(src.clone());

        (member_ty, aset, AttachTree::new(c, ct))
    }
}

impl CollectConstraints for (&ast::Fn, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        todo!()
    }
}

impl CollectConstraints for (&For, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        todo!()
    }
}

impl CollectConstraints for (&If, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        todo!()
    }
}

impl CollectConstraints for (&List, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(list, src) = self;
        let ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let el_ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];

        for item in list.items.iter() {
            let (item_ty, item_aset, item_ct) = item.collect_constraints(mono_tys, srcmap, tcx);
            let c = EqConstraint::new(el_ty.clone(), item_ty).with_src(src.clone());
            cts.push(ParentAttachTree::new(c, item_ct));
            aset.extend(item_aset);
        }

        let c = EqConstraint::new(ty.clone(), Ty::list(el_ty));
        let ct = AttachTree::new(c, NodeTree::new(cts));
        (ty, aset, ct)
    }
}

impl CollectConstraints for (&Literal, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(lit, src) = self;
        let mut ctree = ConstraintTree::empty();
        let t = match &lit {
            Literal::Integer { size, signed, .. } => {
                if *size != 0 {
                    let sign = if !signed { "u" } else { "i" };
                    Ty::con(format!("{}{}", sign, size))
                } else {
                    let t = Ty::Var(tcx.tf().with_scope(&src.path));
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
                    let t = Ty::Var(tcx.tf().with_scope(&src.path));
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

        let v = Ty::Var(tcx.tf().with_scope(&src.path));
        let c = EqConstraint::new(v.clone(), t.clone()).with_src(src.clone());
        (v, AssumptionSet::new(), AttachTree::new(c, ctree))
    }
}

impl CollectConstraints for (&Name, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(name, src) = self;
        let t = Ty::Var(tcx.tf().with_scope(&src.path));
        let label = t.to_string();
        let mut aset = AssumptionSet::new();
        aset.add(name.path.clone(), t.clone());
        (t, aset, ReceiverTree::new(label))
    }
}

impl CollectConstraints for (&Path, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(path, src) = self;
        let t = Ty::Var(tcx.tf().with_scope(&src.path));
        let label = t.to_string();
        let mut aset = AssumptionSet::new();
        aset.add(path.clone(), t.clone());
        (t, aset, ReceiverTree::new(label))
    }
}

impl CollectConstraints for (&Range, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(range, src) = self;
        let (start_ty, start_aset, start_ct) =
            range.start.collect_constraints(mono_tys, srcmap, tcx);
        let (end_ty, end_aset, end_ct) = range.end.collect_constraints(mono_tys, srcmap, tcx);
        let ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let el_ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let ct = AttachTree::new(
            EqConstraint::new(ty.clone(), Ty::range(el_ty.clone())).with_src(src.clone()),
            NodeTree::new(vec![
                ParentAttachTree::new(
                    EqConstraint::new(el_ty.clone(), start_ty).with_src(src.clone()),
                    start_ct,
                ),
                ParentAttachTree::new(
                    EqConstraint::new(el_ty.clone(), end_ty).with_src(src.clone()),
                    end_ct,
                ),
            ]),
        );

        let mut aset = AssumptionSet::new();
        aset.extend(start_aset);
        aset.extend(end_aset);

        (ty, aset, ct)
    }
}

impl CollectConstraints for (&Tuple, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(tuple, src) = self;
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];
        let mut tys = vec![];
        for el in tuple.seq.items.iter() {
            let (el_ty, a, ct) = el.collect_constraints(mono_tys, srcmap, tcx);
            tys.push(el_ty);
            aset.extend(a);
            cts.push(ct);
        }
        let t = Ty::Var(tcx.tf().with_scope(&src.path));
        let c = EqConstraint::new(t.clone(), Ty::Tuple(tys));
        let ct = AttachTree::new(c, NodeTree::new(cts));
        (t, aset, ct)
    }
}

impl CollectConstraints for (&While, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        todo!()
    }
}
