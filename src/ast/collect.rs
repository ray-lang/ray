use std::{collections::HashSet, ops::Deref};

use ast::{Extern, Module, Sequence};
use itertools::{Either, Itertools};

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
            EqConstraint, InstConstraint, ProveConstraint, SkolConstraint, VarConstraint,
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
    ) -> (Ty, BindingGroup, TyEnv) {
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
                        let ty = sig.ty.as_ref().unwrap().clone();
                        let fqn = sig.path.clone();
                        (fqn, ty)
                    }
                    d @ _ => unreachable!("Decl::Extern: {:?}", d),
                };

                env.insert(fqn, ty.clone());

                (ty, BindingGroup::empty().with_src(src.clone()), env)
            }
            Decl::Fn(func) => (func, &src, None).collect_decls(mono_tys, srcmap, tcx),
            Decl::Mutable(d) => todo!("collect_decls: Decl::Mutable: {:?}", d),
            Decl::Name(d) => todo!("collect_decls: Decl::Name: {:?}", d),
            Decl::Declare(d) => todo!("collect_decls: Decl::Declare: {:?}", d),
            Decl::FnSig(d) => todo!("collect_decls: Decl::FnSig: {:?}", d),
            Decl::Struct(_) => (
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
                let self_ty = imp.ty.get_ty_param_at(0);
                if let Some(funcs) = &imp.funcs {
                    for func_node in funcs {
                        let src = srcmap.get(func_node);
                        let func = variant!(&func_node.value, if Decl::Fn(f));
                        let (fn_ty, fn_bg, fn_env) =
                            (func, &src, Some(self_ty)).collect_decls(mono_tys, srcmap, tcx);
                        tcx.set_ty(func_node.id, fn_ty);
                        bg.combine(fn_bg);
                        env.extend(fn_env);
                    }
                }

                if let Some(ext) = &imp.externs {
                    for e in ext {
                        let (_, ext_bg, ext_env) = e.collect_decls(mono_tys, srcmap, tcx);
                        bg.combine(ext_bg);
                        env.extend(ext_env);
                    }
                }

                (Ty::unit(), bg, env)
            }
        };

        tcx.set_ty(self.id, ty.clone());
        (ty, bg, env)
    }
}

impl CollectDeclarations for (&ast::Fn, &Source, Option<&Ty>) {
    fn collect_decls(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Ty, BindingGroup, TyEnv) {
        let &(func, src, maybe_self_ty) = self;

        // name, mut params, body, decs
        let name = &func.sig.path;

        // ⟨M⟩, id, A\dom(E),Cl ◃◦•[ TC1,TC2 •] ⊢fb lhs = rhs : {|τ1,...,τn,τ|}
        let fn_tv = tcx.tf().next();
        log::debug!("type of {} = {}", name, fn_tv);

        // LHS
        let mut mono_tys = mono_tys.clone();
        let mut param_tys = vec![];
        let mut param_cts = vec![];
        let mut lhs_env = TyEnv::new();
        for param in func.sig.params.iter() {
            let param_name = param.name().unwrap();
            let (param_ty, param_env, mut param_ct) = param_name.collect_patterns(srcmap, tcx);

            if let Some(self_ty) = maybe_self_ty {
                if param_name.name().unwrap().as_str() == "self" {
                    let c = EqConstraint::new(param_ty.clone(), self_ty.clone());
                    param_ct = AttachTree::new(c, param_ct);
                }
            }

            if let Ty::Var(tv) = &param_ty {
                mono_tys.insert(tv.clone());
            }
            param_tys.push(param_ty.clone());
            param_cts.push(param_ct);
            lhs_env.extend(param_env);
            tcx.set_ty(param.id, param_ty);
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
            env.insert(name.clone(), ty.clone());
        }
        (Ty::Var(fn_tv), bg, env)
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
        for (_, bg, decl_env) in self
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
        log::debug!("sigs: {:?}", sigs);
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
            Expr::Assign(ex) => unreachable!(), // (ex, src).collect_constraints(mono_tys, srcmap, tcx),
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

        tcx.set_ty(self.id, ty.clone());
        (ty, aset, ct)
    }
}

// impl CollectConstraints for (&Assign, &Source) {
//     type Output = Ty;

//     fn collect_constraints(
//         &self,
//         mono_tys: &HashSet<TyVar>,
//         srcmap: &SourceMap,
//         tcx: &mut TyCtx,
//     ) -> (Self::Output, AssumptionSet, ConstraintTree) {
//         todo!()
//     }
// }

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
            .map(|(op, _)| op.ret_ty(&src.path))
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

fn collect_expr_seq<'a, I>(
    exprs: I,
    mono_tys: &HashSet<TyVar>,
    srcmap: &SourceMap,
    tcx: &mut TyCtx,
) -> (Ty, AssumptionSet, ConstraintTree)
where
    I: Iterator<Item = &'a Node<Expr>>,
{
    // SEQ = assign SEQ | expr SEQ | empty
    enum State {
        Exprs,
        Assigns,
    }

    let mut aset = AssumptionSet::new();
    let mut env = TyEnv::new();
    let mut ty = Ty::unit();
    let mut groups = vec![];
    let mut ctrees = vec![];
    let mut state = State::Assigns;

    for expr in exprs {
        let src = srcmap.get(expr);
        if let Expr::Assign(assign) = &expr.value {
            if matches!(state, State::Exprs) {
                let ctree = ConstraintTree::from_vec(ctrees);
                groups.push(BindingGroup::new(TyEnv::new(), aset, ctree));
                let mut bga = BindingGroupAnalysis::new(groups, &env, tcx.tf(), mono_tys);
                let (_, groups_aset, ctree) = bga.analyze();
                log::debug!("groups aset = {:#?}", groups_aset);
                log::debug!("ctree = {:#?}", ctree);
                aset = groups_aset;
                groups = vec![];
                ctrees = vec![ctree];
                state = State::Assigns;
                continue;
            }

            let (lhs_ty, bg, e) =
                (&assign.lhs, assign.rhs.as_ref(), &src).collect_decls(mono_tys, srcmap, tcx);
            tcx.set_ty(expr.id, Ty::unit());
            tcx.set_ty(assign.lhs.id, lhs_ty);

            groups.push(bg);
            env.extend(e);
        } else {
            let (expr_ty, a, ct) = expr.collect_constraints(mono_tys, srcmap, tcx);
            ty = Ty::Var(tcx.tf().with_scope(&src.path));
            tcx.set_ty(expr.id, ty.clone());
            let c = EqConstraint::new(ty.clone(), expr_ty).with_src(src);
            aset.extend(a);
            ctrees.push(AttachTree::new(c, ct));
            state = State::Exprs;
        }
    }

    let ctree = ConstraintTree::from_vec(ctrees);
    if groups.len() != 0 {
        groups.push(BindingGroup::new(TyEnv::new(), aset, ctree));
        let mut bga = BindingGroupAnalysis::new(groups, &env, tcx.tf(), mono_tys);
        let (_, aset, ctree) = bga.analyze();
        log::debug!("bga aset = {:#?}", aset);
        log::debug!("bga ctree = {:#?}", ctree);
        (Ty::unit(), aset, ctree)
    } else {
        (ty, aset, ctree)
    }

    // let mut groups = vec![];
    // let mut env = TyEnv::new();
    // while let Some(expr) = exprs.next() {
    //     if let Expr::Assign(assign) = &expr.value {
    //         let src = srcmap.get(expr);
    //         let (_, bg, e) =
    //             (&assign.lhs, assign.rhs.as_ref(), &src).collect_decls(mono_tys, srcmap, tcx);
    //         groups.push(bg);
    //         env.extend(e);
    //         continue;
    //     }

    //     let mut exprs = std::iter::once(expr).chain(exprs);
    //     let (ty, aset, ctree) = collect_expr_seq(&mut exprs, mono_tys, srcmap, tcx);
    //     groups.insert(0, BindingGroup::new(TyEnv::new(), aset, ctree));
    //     let mut bga = BindingGroupAnalysis::new(groups, &env, tcx.tf(), mono_tys);
    //     let (_, aset, ctree) = bga.analyze();
    //     return (ty, aset, ctree);
    // }

    // (Ty::unit(), AssumptionSet::new(), ConstraintTree::empty())

    // let mut expr;
    // loop {
    //     if let Some(e) = exprs.next() {
    //         expr = e;
    //         if let Expr::Assign(a) = &ex.value {
    //             // handle assign
    //         } else {
    //             break;
    //         }
    //     }
    // }

    // loop {
    //     // handle expression

    //     if let Some(e) = exprs.next() {
    //         expr = e;
    //     } else {
    //         break;
    //     }
    // }

    // if assigns.len() == 0 {
    //     // let mut ty = Ty::unit();
    //     // let mut aset = AssumptionSet::new();
    //     // let mut ctree = ConstraintTree::empty();
    //     // for stmt in rest {
    //     //     let (stmt_ty, a, ct) = stmt.collect_constraints(mono_tys, srcmap, tcx);
    //     //     let b = Ty::Var(tcx.tf().with_scope(&src.path));
    //     //     let src = srcmap.get(stmt);
    //     //     let c = EqConstraint::new(b.clone(), stmt_ty).with_src(src);
    //     //     ty = b;
    //     //     aset.extend(a);
    //     //     cts.push(AttachTree::new(c, ct));
    //     // }
    //     // return (ty, , )
    // }

    // let mut groups = vec![];
    // let mut env = TyEnv::new();
    // for assign in assigns {
    //     let src = srcmap.get(&assign);
    //     let (_, bg, e) =
    //         (&assign.lhs, assign.rhs.as_ref(), &src).collect_decls(mono_tys, srcmap, tcx);
    //     groups.push(bg);
    //     env.extend(e);
    // }

    // let (ty, aset, ctree) = collect_expr_seq(rest.into_iter(), mono_tys, srcmap, tcx);
    // groups.insert(0, BindingGroup::new(TyEnv::new(), aset, ctree));
    // let mut bga = BindingGroupAnalysis::new(groups, &env, tcx.tf(), mono_tys);
    // let (_, aset, ctree) = bga.analyze();
    // (ty, aset, ctree)

    // let src = srcmap.get(head);
    // if let Expr::Assign(assign) = &head.value {
    //     let (lhs_ty, bg, env) =
    //         (&assign.lhs, assign.rhs.as_ref(), &src).collect_decls(mono_tys, srcmap, tcx);
    //     tcx.set_ty(assign.lhs.id, lhs_ty);

    //     let (ty, aset, ctree) = if let Some((next, tail)) = tail.split_first() {
    //         collect_block(next, tail, aset, mono_tys, srcmap, tcx)
    //     } else {
    //         (Ty::unit(), aset, ConstraintTree::empty())
    //     };

    //     let groups = vec![
    //         BindingGroup::new(TyEnv::new(), aset, ctree).with_src(src.clone()),
    //         bg,
    //     ];
    //     let mut bga = BindingGroupAnalysis::new(groups, &env, tcx.tf(), mono_tys);
    //     let (_, aset, ctree) = bga.analyze();
    //     (ty, aset, ctree)
    // } else {
    //     let (ty, a, ct) = head.collect_constraints(mono_tys, srcmap, tcx);
    //     aset.extend(a);

    //     let v = Ty::Var(tcx.tf().with_scope(&src.path));
    //     let ctree = AttachTree::new(EqConstraint::new(v.clone(), ty).with_src(src), ct);

    //     if let Some((head, tail)) = tail.split_first() {
    //         todo!()
    //     }

    //     (v, aset, ctree)
    // }
}

impl CollectConstraints for (&Block, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        mono_tys: &HashSet<TyVar>,
        srcmap: &SourceMap,
        tcx: &mut TyCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(block, _) = self;
        collect_expr_seq(block.stmts.iter(), mono_tys, srcmap, tcx)
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
            tcx.set_ty(node.id, member_ty.clone());
            (member_ty, ct1)
        } else {
            let (lhs_ty, fun_aset, ct1) = call.lhs.collect_constraints(mono_tys, srcmap, tcx);
            log::debug!("type of {}: {}", call.lhs, lhs_ty);
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
        log::debug!("call aset: {:#?}", aset);

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
        let ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let c1 = InstConstraint::new(ty.clone(), curly.ty.clone()).with_src(src.clone());
        let mut cts = vec![AttachTree::new(c1, ConstraintTree::empty())];
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
                    ty.clone(),
                    name.path.to_string(),
                    field_ty.clone(),
                ))
                .with_src(src.clone()),
                ct,
            ));
            tcx.set_ty(el.id, field_ty);
        }

        let ty_args = (0..curly.ty.get_ty_params().len())
            .into_iter()
            .map(|_| Ty::Var(tcx.tf().with_scope(&src.path)))
            .collect();

        let fqn = curly.lhs.as_ref().unwrap().to_string();
        let c2 = EqConstraint::new(ty.clone(), Ty::Projection(fqn, ty_args)).with_src(src.clone());

        let ct = AttachTree::new(c2, NodeTree::new(cts));

        (ty, aset, ct)
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
            member_ty.clone(),
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
        let &(if_ex, src) = self;
        let mut cts = vec![];
        let mut aset = AssumptionSet::new();
        let ty = Ty::Var(tcx.tf().with_scope(&src.path));
        log::debug!("if ty = {}", ty);

        let (cond_ty, cond_aset, cond_ct) = if_ex.cond.collect_constraints(mono_tys, srcmap, tcx);
        aset.extend(cond_aset);

        cts.push(ParentAttachTree::new(
            EqConstraint::new(cond_ty, Ty::bool()).with_src(src.clone()),
            cond_ct,
        ));
        let (then_ty, then_aset, then_ct) = if_ex.then.collect_constraints(mono_tys, srcmap, tcx);
        aset.extend(then_aset);
        log::debug!("then_ty = {}", then_ty);

        if let Some(els) = if_ex.els.as_deref() {
            let (else_ty, else_aset, else_ct) = els.collect_constraints(mono_tys, srcmap, tcx);
            aset.extend(else_aset);
            log::debug!("else_ty = {}", else_ty);
            cts.push(ParentAttachTree::new(
                EqConstraint::new(then_ty, ty.clone()).with_src(src.clone()),
                then_ct,
            ));
            cts.push(ParentAttachTree::new(
                EqConstraint::new(else_ty, ty.clone()).with_src(src.clone()),
                else_ct,
            ));
        } else {
            cts.push(ParentAttachTree::new(
                EqConstraint::new(Ty::nilable(then_ty), ty.clone()).with_src(src.clone()),
                then_ct,
            ));
        }

        (ty, aset, NodeTree::new(cts))
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

        let ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let c = EqConstraint::new(ty.clone(), t.clone()).with_src(src.clone());
        (ty, AssumptionSet::new(), AttachTree::new(c, ctree))
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
        let ty = Ty::Var(tcx.tf().with_scope(&src.path));
        let c = EqConstraint::new(ty.clone(), Ty::Tuple(tys));
        let ct = AttachTree::new(c, NodeTree::new(cts));
        (ty, aset, ct)
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
