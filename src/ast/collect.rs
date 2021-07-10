use std::{collections::HashSet, iter::Peekable, ops::Deref};

use ast::Module;
use itertools::Itertools;

use crate::{
    ast,
    span::{Source, SourceMap},
    typing::{
        assumptions::AssumptionSet,
        binding::{BindingGroup, BindingGroupAnalysis},
        collect::{CollectConstraints, CollectCtx, CollectDeclarations, CollectPatterns},
        constraints::{
            tree::{AttachTree, ConstraintTree, NodeTree, ParentAttachTree, ReceiverTree},
            EqConstraint, InstConstraint, ProveConstraint, SkolConstraint,
        },
        predicate::TyPredicate,
        state::TyEnv,
        ty::{LiteralKind, Ty},
        TyCtx,
    },
};

use super::{
    asm::{Asm, AsmOperand},
    BinOp, Block, Call, Cast, Curly, CurlyElement, Decl, Dot, Expr, For, If, List, Literal, Name,
    New, Node, Path, Pattern, Range, Tuple, UnaryOp, While,
};

impl CollectPatterns for Node<Pattern> {
    fn collect_patterns(&self, srcmap: &SourceMap, tcx: &mut TyCtx) -> (Ty, TyEnv, ConstraintTree) {
        match &self.value {
            Pattern::Name(n) => n.path.collect_patterns(srcmap, tcx),
            Pattern::Sequence(_) => todo!("collect patterns: {}", self),
            Pattern::Tuple(_) => todo!("collect patterns: {}", self),
            Pattern::Deref(n) => {
                let src = srcmap.get(self);
                let (ptr_ty, env, ctree) = n.path.collect_patterns(srcmap, tcx);
                let ty = Ty::Var(tcx.tf().next());
                let c = EqConstraint::new(ptr_ty, Ty::ptr(ty.clone())).with_src(src);
                tcx.set_ty(self.id, ty.clone());
                (ty, env, AttachTree::new(c, ctree))
            }
        }
    }
}

impl CollectDeclarations for Node<Decl> {
    type Output = Vec<(BindingGroup, TyEnv)>;

    fn collect_decls(&self, ctx: &mut CollectCtx) -> Vec<(BindingGroup, TyEnv)> {
        let src = ctx.srcmap.get(self);
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
            Decl::Fn(func) => (func, &src, None).collect_decls(ctx),
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
                    log::debug!("trait func: {}", func.path);
                    env.insert(func.path.clone(), func.ty.clone().unwrap());
                }

                (Ty::unit(), BindingGroup::empty().with_src(src.clone()), env)
            }
            Decl::TypeAlias(d, _) => todo!("collect_decls: Decl::TypeAlias: {:?}", d),
            Decl::Impl(imp) => {
                let mut decl_pairs = vec![];

                let self_ty = if imp.is_object {
                    imp.ty.deref()
                } else {
                    imp.ty.get_ty_param_at(0)
                };
                if let Some(funcs) = &imp.funcs {
                    for func_node in funcs {
                        let src = ctx.srcmap.get(func_node);
                        let func = variant!(&func_node.value, if Decl::Fn(f));
                        let self_ty = if func.sig.params.len() != 0 {
                            Some(self_ty)
                        } else {
                            // a impl function with no parameters is static
                            None
                        };
                        let (fn_ty, fn_bg, fn_env) = (func, &src, self_ty).collect_decls(ctx);
                        ctx.tcx.set_ty(func_node.id, fn_ty);
                        log::debug!("fn_bg = {:?}", fn_bg);
                        log::debug!("fn_env = {:?}", fn_env);

                        decl_pairs.push((fn_bg, fn_env));
                    }
                }

                if let Some(consts) = &imp.consts {
                    for const_node in consts {
                        let src = ctx.srcmap.get(const_node);
                        let (const_ty, const_bg, const_env) =
                            (&const_node.lhs, const_node.rhs.as_ref(), &src).collect_decls(ctx);
                        // if let Some(path) = const_node.lhs.path() {
                        //     const_env.insert(path.clone(), const_ty.clone());
                        // }

                        ctx.tcx.set_ty(const_node.id, Ty::unit());
                        ctx.tcx.set_ty(const_node.lhs.id, const_ty);
                        log::debug!("const_bg = {:?}", const_bg);
                        log::debug!("const_env = {:?}", const_env);
                        decl_pairs.push((const_bg, const_env));
                    }
                }

                if let Some(ext) = &imp.externs {
                    for (ext_bg, ext_env) in ext.iter().flat_map(|e| e.collect_decls(ctx)) {
                        decl_pairs.push((ext_bg, ext_env));
                    }
                }

                return decl_pairs;
            }
        };

        log::debug!("set type of: {:?}", self);
        ctx.tcx.set_ty(self.id, ty);
        vec![(bg, env)]
    }
}

impl CollectDeclarations for (&ast::Fn, &Source, Option<&Ty>) {
    type Output = (Ty, BindingGroup, TyEnv);

    fn collect_decls(&self, ctx: &mut CollectCtx) -> (Ty, BindingGroup, TyEnv) {
        let &(func, src, maybe_self_ty) = self;

        // name, mut params, body, decs
        let name = &func.sig.path;

        // ⟨M⟩, id, A\dom(E),Cl ◃◦•[ TC1,TC2 •] ⊢fb lhs = rhs : {|τ1,...,τn,τ|}
        let fn_tv = ctx.tcx.tf().next();
        log::debug!("type of {} = {}", name, fn_tv);

        // LHS
        let mut mono_tys = ctx.mono_tys.clone();
        let mut param_tys = vec![];
        let mut param_cts = vec![];
        let mut lhs_env = TyEnv::new();
        for param in func.sig.params.iter() {
            let param_name = param.name().unwrap();
            let (param_ty, param_env, mut param_ct) =
                param_name.collect_patterns(ctx.srcmap, ctx.tcx);

            if let Some(self_ty) = maybe_self_ty {
                if param_name.name().unwrap().as_str() == "self" {
                    let src = ctx.srcmap.get(param);
                    let c = EqConstraint::new(param_ty.clone(), self_ty.clone()).with_src(src);
                    param_ct = AttachTree::new(c, param_ct);
                }
            }

            if let Ty::Var(tv) = &param_ty {
                mono_tys.insert(tv.clone());
            }
            param_tys.push(param_ty.clone());
            param_cts.push(param_ct);
            lhs_env.extend(param_env);
            ctx.tcx.set_ty(param.id, param_ty);
        }

        // RHS
        // ⟨M + ftv(Cl)⟩,A,TC2 ⊢rhs rhs : τ
        let mut ctx = CollectCtx {
            mono_tys: &mono_tys,
            srcmap: ctx.srcmap,
            tcx: ctx.tcx,
            defs: ctx.defs.clone(),
        };
        let (body_ty, aset, body_ct) = func.body.as_deref().unwrap().collect_constraints(&mut ctx);

        let fn_ty = Ty::Func(param_tys, Box::new(body_ty));

        let params_ct = NodeTree::new(param_cts);
        let cl = EqConstraint::lift(&aset, &lhs_env)
            .into_iter()
            .map(|(l, c)| (l, c.with_src(src.clone())))
            .collect();

        let ct = NodeTree::new(vec![
            ReceiverTree::new(fn_tv.to_string()),
            ParentAttachTree::new(
                EqConstraint::new(Ty::Var(fn_tv.clone()), fn_ty).with_src(src.clone()),
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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let mut bgroups = vec![];
        let mut defs = TyEnv::new();
        for (bg, decl_env) in self.decls.iter().flat_map(|d| d.collect_decls(ctx)) {
            log::debug!("bg = {:#?}", bg);
            log::debug!("decl_env = {:#?}", decl_env);
            bgroups.push(bg);
            defs.extend(decl_env);
        }

        let mono_tys = HashSet::new();
        log::debug!("defs: {:?}", defs);
        ctx.defs.extend(defs);
        let mut bga = BindingGroupAnalysis::new(bgroups, &ctx.defs, ctx.tcx.tf(), &mono_tys);
        let (_, aset, ct) = bga.analyze();
        log::debug!("module aset: {:?}", aset);
        log::debug!("sigs: {:?}", ctx.defs);
        let cl = InstConstraint::lift(&aset, &ctx.defs);
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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(b, _) = self;
        let (out, aset, ct) = b.collect_constraints(ctx);
        (out, aset, ct)
    }
}

impl CollectConstraints for Node<Expr> {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let src = &ctx.srcmap.get(self);
        let (ty, aset, ct) = match &self.value {
            Expr::Assign(_) => unreachable!(),
            Expr::Asm(ex) => (ex, src).collect_constraints(ctx),
            Expr::BinOp(ex) => (ex, src).collect_constraints(ctx),
            Expr::Block(ex) => (ex, src).collect_constraints(ctx),
            Expr::Break(ex) => {
                if let Some(ex) = ex {
                    let src = &ctx.srcmap.get(ex);
                    (ex, src).collect_constraints(ctx)
                } else {
                    (Ty::unit(), AssumptionSet::new(), ConstraintTree::empty())
                }
            }
            Expr::Call(ex) => (ex, src).collect_constraints(ctx),
            Expr::Cast(ex) => (ex, src).collect_constraints(ctx),
            Expr::Closure(_) => todo!(),
            Expr::Curly(ex) => (ex, src).collect_constraints(ctx),
            Expr::DefaultValue(_) => todo!(),
            Expr::Dot(ex) => (ex, src).collect_constraints(ctx),
            Expr::Fn(_) => todo!(),
            Expr::For(ex) => (ex, src).collect_constraints(ctx),
            Expr::If(ex) => (ex, src).collect_constraints(ctx),
            Expr::Index(_) => {
                todo!()
                // (ex, src).collect_constraints(ctx)
            }
            Expr::Labeled(_, _) => todo!(),
            Expr::List(ex) => (ex, src).collect_constraints(ctx),
            Expr::Literal(ex) => (ex, src).collect_constraints(ctx),
            Expr::Loop(_) => todo!(),
            Expr::Name(ex) => (ex, src).collect_constraints(ctx),
            Expr::New(ex) => (ex, src).collect_constraints(ctx),
            Expr::Pattern(ex) => (ex, src).collect_constraints(ctx),
            Expr::Path(ex) => (ex, src).collect_constraints(ctx),
            Expr::Paren(ex) => (ex, src).collect_constraints(ctx),
            Expr::Range(ex) => (ex, src).collect_constraints(ctx),
            Expr::Return(_) => todo!(),
            Expr::Sequence(_) => todo!(),
            Expr::Tuple(ex) => (ex, src).collect_constraints(ctx),
            Expr::Type(_) => todo!(),
            Expr::TypeAnnotated(ex, ty) => {
                let anno_ty = ty.deref().deref().clone();
                let (ty, aset, ctree) = ex.collect_constraints(ctx);
                let c1 = SkolConstraint::new(ctx.mono_tys.clone(), ty, anno_ty.clone())
                    .with_src(src.clone());
                let b = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
                let c2 = InstConstraint::new(b.clone(), anno_ty.clone()).with_src(src.clone());
                (
                    anno_ty,
                    aset,
                    AttachTree::new(c2, NodeTree::new(vec![ParentAttachTree::new(c1, ctree)])),
                )
            }
            Expr::UnaryOp(ex) => (ex, src).collect_constraints(ctx),
            Expr::Unsafe(_) => todo!(),
            Expr::While(ex) => (ex, src).collect_constraints(ctx),
        };

        ctx.tcx.set_ty(self.id, ty.clone());
        (ty, aset, ct)
    }
}

impl CollectConstraints for (&Asm, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(asm, src) = self;
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];
        for (_, rands) in asm.inst.iter() {
            for v in rands.iter() {
                let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
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
        let v = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let mut cs = vec![];
        if let Some(ty) = asm.ret_ty.as_deref() {
            cs.push(EqConstraint::new(ty.clone(), v.clone()).with_src(src.clone()));
        }

        cs.push(EqConstraint::new(last_ty, v.clone()).with_src(src.clone()));
        cts.push(ConstraintTree::list(cs));

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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(binop, src) = self;
        let (lhs_ty, lhs_aset, lhs_ct) = binop.lhs.collect_constraints(ctx);
        let (rhs_ty, rhs_aset, rhs_ct) = binop.rhs.collect_constraints(ctx);

        let op_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        ctx.tcx.set_ty(binop.op.id, op_ty.clone());

        let result_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        let name = binop.op.to_string();
        let (fqn, _) = ctx.tcx.lookup_infix_op(&name).cloned().unwrap();

        log::debug!("binop fqn: {}", fqn);

        let mut aset = lhs_aset;
        aset.add(fqn, op_ty.clone());
        aset.extend(rhs_aset);

        let op_src = ctx.srcmap.get(&binop.op);
        let op_ct = ReceiverTree::new(op_ty.to_string());
        let eq = EqConstraint::new(
            op_ty,
            Ty::Func(vec![lhs_ty, rhs_ty], Box::new(result_ty.clone())),
        )
        .with_src(op_src);

        (
            result_ty,
            aset,
            AttachTree::new(eq, NodeTree::new(vec![lhs_ct, op_ct, rhs_ct])),
        )
    }
}

// fn collect_expr_seq<'a, I>(exprs: I, ctx: &mut CollectCtx) -> (Ty, AssumptionSet, ConstraintTree)
// where
//     I: Iterator<Item = &'a Node<Expr>>,
// {
//     // SEQ = assign SEQ | expr SEQ | empty
//     enum State {
//         Exprs,
//         Assigns,
//     }

//     let mut aset = AssumptionSet::new();
//     let mut ty = Ty::unit();
//     let mut groups = vec![];
//     let mut ctrees = vec![];
//     let mut state = State::Assigns;

//     for expr in exprs {
//         let src = ctx.srcmap.get(expr);
//         if let Expr::Assign(assign) = &expr.value {
//             let (lhs_ty, bg, _) = (&assign.lhs, assign.rhs.as_ref(), &src).collect_decls(ctx);
//             ctx.tcx.set_ty(expr.id, Ty::unit());
//             ctx.tcx.set_ty(assign.lhs.id, lhs_ty);

//             // then check if there are any variables in the group
//             // that have already been defined and create constraints
//             let mut ctree = ConstraintTree::empty();
//             let lhs_src = ctx.srcmap.get(&assign.lhs);
//             for (var, ty) in bg.env().iter() {
//                 if let Some(other_ty) = ctx.defs.get(&var) {
//                     log::debug!("already defined: {} :: {}", var, other_ty);
//                     log::debug!("creating equality constraint: {} == {}", ty, other_ty);

//                     // create an equality constraint
//                     ctree = AttachTree::new(
//                         EqConstraint::new(ty.clone(), other_ty.clone()).with_src(lhs_src.clone()),
//                         ctree,
//                     );
//                 } else {
//                     // otherwise, add them to the definitions
//                     ctx.defs.insert(var.clone(), ty.clone());
//                 }
//             }

//             if matches!(state, State::Exprs) {
//                 let ctree = ConstraintTree::from_vec(ctrees);
//                 groups.push(BindingGroup::new(TyEnv::new(), aset, ctree));
//                 log::debug!("env = {:#?}", ctx.defs);
//                 let mut bga =
//                     BindingGroupAnalysis::new(groups, &ctx.defs, ctx.tcx.tf(), ctx.mono_tys);
//                 let (_, groups_aset, ctree) = bga.analyze();
//                 log::debug!("groups aset = {:#?}", groups_aset);
//                 log::debug!("ctree = {:#?}", ctree);
//                 aset = groups_aset;
//                 groups = vec![];
//                 ctrees = vec![ctree];
//                 state = State::Assigns;
//             }

//             groups.push(bg);
//             ctrees.push(ctree);
//         } else {
//             let (expr_ty, a, ct) = expr.collect_constraints(ctx);
//             ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
//             ctx.tcx.set_ty(expr.id, ty.clone());
//             let c = EqConstraint::new(ty.clone(), expr_ty).with_src(src);
//             aset.extend(a);
//             ctrees.push(AttachTree::new(c, ct));
//             state = State::Exprs;
//         }
//     }

//     let ctree = ConstraintTree::from_vec(ctrees);
//     let ty = if matches!(state, State::Exprs) {
//         ty
//     } else {
//         Ty::unit()
//     };

//     if groups.len() != 0 {
//         log::debug!("aset = {:#?}", aset);
//         log::debug!("env = {:#?}", ctx.defs);
//         log::debug!("groups = {:#?}", groups);
//         groups.push(BindingGroup::new(TyEnv::new(), aset, ctree));
//         let mut bga = BindingGroupAnalysis::new(groups, &ctx.defs, ctx.tcx.tf(), ctx.mono_tys);
//         let (_, aset, ctree) = bga.analyze();
//         log::debug!("bga aset = {:#?}", aset);
//         log::debug!("bga ctree = {:#?}", ctree);
//         (ty, aset, ctree)
//     } else {
//         (ty, aset, ctree)
//     }
// }

impl CollectConstraints for (&Block, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        // fn collect_expr_seq<'a, I>(
        //     mut seq: Peekable<I>,
        //     ctx: &mut CollectCtx,
        // ) -> (Option<Ty>, AssumptionSet, ConstraintTree)
        // where
        //     I: Iterator<Item = &'a Node<Expr>>,
        // {
        //     // peek the next element
        //     let next = unless!(seq.peek(), else {
        //         return (None, AssumptionSet::new(), ConstraintTree::empty());
        //     });

        //     // check if the next element is not an assignment
        //     if !matches!(next.value, Expr::Assign(_)) {
        //         let (expr_ty, mut aset, expr_ct) = seq.next().unwrap().collect_constraints(ctx);
        //         log::debug!("aset = {:?}", aset);
        //         let (seq_ty, rest_aset, seq_ct) = collect_expr_seq(seq, ctx);
        //         aset.extend(rest_aset);
        //         return (
        //             Some(seq_ty.unwrap_or(expr_ty)),
        //             aset,
        //             NodeTree::new(vec![expr_ct, seq_ct]),
        //         );
        //     }

        //     // collect binding groups and environments from declarations
        //     let (decl_bgroups, decl_envs): (Vec<_>, Vec<_>) = seq
        //         .peeking_take_while(|node| matches!(node.value, Expr::Assign(_)))
        //         .map(|node| {
        //             let src = ctx.srcmap.get(node);
        //             let assign = variant!(&node.value, if Expr::Assign(assign));
        //             let (lhs_ty, bg, env) =
        //                 (&assign.lhs, assign.rhs.as_ref(), &src).collect_decls(ctx);
        //             log::debug!("lhs_ty = {:?}", lhs_ty);
        //             log::debug!("bg = {:?}", bg);
        //             log::debug!("env = {:?}", env);

        //             ctx.tcx.set_ty(node.id, Ty::unit());
        //             ctx.tcx.set_ty(assign.lhs.id, lhs_ty);
        //             (bg, env)
        //         })
        //         .unzip();

        //     // then collect the rest
        //     let (ty, aset, ctree) = collect_expr_seq(seq, ctx);
        //     let mut bg_groups = vec![BindingGroup::new(TyEnv::new(), aset, ctree)];
        //     bg_groups.extend(decl_bgroups);

        //     let mut defs = ctx.defs.clone();
        //     for env in decl_envs {
        //         defs.extend(env);
        //     }

        //     let mut bga = BindingGroupAnalysis::new(bg_groups, &defs, ctx.tcx.tf(), ctx.mono_tys);
        //     let (_, aset, ctree) = bga.analyze();
        //     log::debug!("ty = {:?}", ty);
        //     log::debug!("aset = {:?}", aset);
        //     (ty, aset, ctree)
        // }
        fn collect_expr_seq<'a, I>(
            mut seq: Peekable<I>,
            ctx: &mut CollectCtx,
        ) -> (Option<Ty>, AssumptionSet, ConstraintTree)
        where
            I: Iterator<Item = &'a Node<Expr>>,
        {
            // peek the next element
            let next = unless!(seq.peek(), else {
                return (None, AssumptionSet::new(), ConstraintTree::empty());
            });

            // check if the next element is not an assignment
            if !matches!(next.value, Expr::Assign(_)) {
                let (expr_ty, mut aset, expr_ct) = seq.next().unwrap().collect_constraints(ctx);
                log::debug!("aset = {:?}", aset);
                let (seq_ty, rest_aset, seq_ct) = collect_expr_seq(seq, ctx);
                aset.extend(rest_aset);
                return (
                    Some(seq_ty.unwrap_or(expr_ty)),
                    aset,
                    NodeTree::new(vec![expr_ct, seq_ct]),
                );
            }

            // collect binding groups and environments from declarations
            let node = seq.next().unwrap();
            ctx.tcx.set_ty(node.id, Ty::unit());

            let src = ctx.srcmap.get(node);
            let assign = variant!(&node.value, if Expr::Assign(assign));

            let (lhs_ty, env, ct1) = assign.lhs.collect_patterns(ctx.srcmap, ctx.tcx);
            let (rhs_ty, mut rhs_aset, ct2) = assign.rhs.collect_constraints(ctx);
            log::debug!("rhs_aset: {:?}", rhs_aset);
            let eq = EqConstraint::new(lhs_ty.clone(), rhs_ty).with_src(src);
            log::debug!("eq: {:?}", eq);
            ctx.tcx.set_ty(assign.lhs.id, lhs_ty);

            // then collect the rest
            let (ty, rest_aset, ct3) = collect_expr_seq(seq, ctx);
            let cl = EqConstraint::lift(&rest_aset, &env);
            rhs_aset.extend(rest_aset - env.keys());
            log::debug!("rhs_aset: {:?}", rhs_aset);

            let ctree = AttachTree::new(eq, NodeTree::new(vec![ct1, ct2, ct3]).spread_list(cl));

            (Some(ty.unwrap_or_default()), rhs_aset, ctree)

            // let mut bg_groups = vec![BindingGroup::new(TyEnv::new(), aset, ctree)];
            // bg_groups.extend(decl_bgroups);

            // let mut defs = ctx.defs.clone();
            // for env in decl_envs {
            //     defs.extend(env);
            // }

            // let mut bga = BindingGroupAnalysis::new(bg_groups, &defs, ctx.tcx.tf(), ctx.mono_tys);
            // let (_, aset, ctree) = bga.analyze();
            // log::debug!("ty = {:?}", ty);
            // log::debug!("aset = {:?}", aset);
            // (ty, aset, ctree)
        }

        let &(block, _) = self;
        let (ty, aset, ctree) =
            ctx.with_ctx(|ctx| collect_expr_seq(block.stmts.iter().peekable(), ctx));
        log::debug!("aset = {:?}", aset);
        (ty.unwrap_or_default(), aset, ctree)
    }
}

impl CollectConstraints for (&Call, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(call, src) = self;
        let mut aset = AssumptionSet::new();
        let mut arg_tys = vec![];
        let mut arg_cts = vec![];

        let (lhs_ty, ct1) = if let Expr::Dot(dot) = &call.lhs.value {
            let (self_ty, self_aset, mut ct1) = dot.lhs.collect_constraints(ctx);
            arg_tys.push(self_ty.clone());
            aset.extend(self_aset);

            let src = ctx.srcmap.get(&dot.lhs);
            let member_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
            let name = dot.rhs.path.to_string();
            log::debug!("name: {}", name);
            let fqn = if let Some(fqn) = ctx.tcx.lookup_fqn(&name) {
                fqn.clone()
            } else {
                Path::from(format!(
                    "{}::{}",
                    self_ty.clone().get_path().unwrap(),
                    dot.rhs.path
                ))
            };

            log::debug!("fqn: {}", fqn);

            aset.add(fqn.clone(), member_ty.clone());
            ct1 = NodeTree::new(vec![ReceiverTree::new(member_ty.to_string()), ct1]);
            ctx.tcx.set_ty(call.lhs.id, member_ty.clone());
            (member_ty, ct1)
        } else {
            let (lhs_ty, fun_aset, ct1) = call.lhs.collect_constraints(ctx);
            log::debug!("type of {}: {}", call.lhs, lhs_ty);
            log::debug!("fun_aset = {:#?}", fun_aset);
            aset.extend(fun_aset);
            (lhs_ty, ct1)
        };

        for (arg_ty, a, ct) in call.args.items.iter().map(|a| a.collect_constraints(ctx)) {
            aset.extend(a);
            arg_tys.push(arg_ty);
            arg_cts.push(ct);
        }

        let ret_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(cast, src) = self;
        let (_, a, ct) = cast.lhs.collect_constraints(ctx);
        let v = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        // TODO: should there be a cast constraint?
        let c = EqConstraint::new(v.clone(), cast.ty.deref().clone()).with_src(src.clone());
        (v, a, AttachTree::new(c, ct))
    }
}

impl CollectConstraints for (&Curly, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(curly, src) = self;
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let c1 = InstConstraint::new(ty.clone(), curly.ty.clone()).with_src(src.clone());
        let mut cts = vec![AttachTree::new(c1, ConstraintTree::empty())];
        let mut aset = AssumptionSet::new();
        for el in curly.elements.iter() {
            let (name, (field_ty, a, ct)) = match &el.value {
                CurlyElement::Labeled(name, field) => (name, field.collect_constraints(ctx)),
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
            ctx.tcx.set_ty(el.id, field_ty);
        }

        let ty_args = (0..curly.ty.get_ty_params().len())
            .into_iter()
            .map(|_| Ty::Var(ctx.tcx.tf().with_scope(&src.path)))
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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(dot, src) = self;
        let (lhs_ty, aset, ct) = dot.lhs.collect_constraints(ctx);
        let member_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
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
        _: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        todo!()
    }
}

impl CollectConstraints for (&For, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        _: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        todo!()
    }
}

impl CollectConstraints for (&If, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(if_ex, src) = self;
        let mut cts = vec![];
        let mut aset = AssumptionSet::new();
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        log::debug!("if ty = {}", ty);

        let (cond_ty, cond_aset, cond_ct) = if_ex.cond.collect_constraints(ctx);
        aset.extend(cond_aset);

        let cond_src = ctx.srcmap.get(&if_ex.cond);
        cts.push(ParentAttachTree::new(
            EqConstraint::new(cond_ty, Ty::bool()).with_src(cond_src),
            cond_ct,
        ));
        let (then_ty, then_aset, then_ct) = if_ex.then.collect_constraints(ctx);
        aset.extend(then_aset);
        log::debug!("then_ty = {}", then_ty);

        let then_src = ctx.srcmap.get(&if_ex.then);
        if let Some(els) = if_ex.els.as_deref() {
            let (else_ty, else_aset, else_ct) = els.collect_constraints(ctx);
            let else_src = ctx.srcmap.get(els);
            aset.extend(else_aset);
            log::debug!("else_ty = {}", else_ty);
            cts.push(ParentAttachTree::new(
                EqConstraint::new(then_ty, ty.clone()).with_src(then_src),
                then_ct,
            ));
            cts.push(ParentAttachTree::new(
                EqConstraint::new(else_ty, ty.clone()).with_src(else_src),
                else_ct,
            ));
        } else {
            cts.push(ParentAttachTree::new(
                EqConstraint::new(Ty::nilable(then_ty), ty.clone()).with_src(then_src),
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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(list, src) = self;
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let el_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];

        for item in list.items.iter() {
            let (item_ty, item_aset, item_ct) = item.collect_constraints(ctx);
            let c = EqConstraint::new(el_ty.clone(), item_ty).with_src(src.clone());
            cts.push(ParentAttachTree::new(c, item_ct));
            aset.extend(item_aset);
        }

        let c = EqConstraint::new(ty.clone(), Ty::list(el_ty)).with_src(src.clone());
        let ct = AttachTree::new(c, NodeTree::new(cts));
        (ty, aset, ct)
    }
}

impl CollectConstraints for (&Literal, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(lit, src) = self;
        let mut ctree = ConstraintTree::empty();
        let literal_ty = match &lit {
            Literal::Integer { size, signed, .. } => {
                if *size != 0 {
                    let sign = if !signed { "u" } else { "i" };
                    Ty::con(format!("{}{}", sign, size))
                } else {
                    let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
                    ctree = AttachTree::list(
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
                    let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
                    ctree = AttachTree::list(
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

        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        log::debug!("ty = {}", ty);
        log::debug!("literal_ty = {}", literal_ty);
        let c = EqConstraint::new(ty.clone(), literal_ty).with_src(src.clone());
        (ty, AssumptionSet::new(), AttachTree::new(c, ctree))
    }
}

impl CollectConstraints for (&Name, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(name, src) = self;
        log::debug!("path: {}", name.path);
        let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let label = t.to_string();
        let mut aset = AssumptionSet::new();
        aset.add(name.path.clone(), t.clone());
        (t, aset, ReceiverTree::new(label))
    }
}

impl CollectConstraints for (&New, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(new, src) = self;
        let result_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let pointee_ty = new.ty.deref().deref().clone();
        let mut cs = vec![];
        // let mut ct = AttachTree::new(eq, ConstraintTree::empty());
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];
        if let Some(count) = &new.count {
            let count_src = ctx.srcmap.get(count);
            let (count_ty, count_aset, count_ct) = count.collect_constraints(ctx);
            let c = EqConstraint::new(count_ty, Ty::uint()).with_src(count_src);
            log::debug!("count constraint: {:?}", c);
            log::debug!("count ctree: {:#?}", count_ct);
            aset.extend(count_aset);
            cs.push(c);
            cts.push(count_ct)
        }

        cs.push(EqConstraint::new(
            result_ty.clone(),
            Ty::Ptr(Box::new(pointee_ty)),
        ));

        (result_ty, aset, AttachTree::list(cs, NodeTree::new(cts)))
    }
}

impl CollectConstraints for (&Pattern, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(pattern, src) = self;
        let mut aset = AssumptionSet::new();
        let (ty, ctree) = match pattern {
            Pattern::Name(name) | Pattern::Deref(name) => {
                let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
                let label = ty.to_string();
                aset.add(name.path.clone(), ty.clone());
                let ctree = ReceiverTree::new(label);
                (ty, ctree)
            }
            Pattern::Sequence(_) => todo!(),
            Pattern::Tuple(_) => todo!(),
        };
        (ty, aset, ctree)
    }
}

impl CollectConstraints for (&Path, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(path, src) = self;
        log::debug!("path = {}", path);
        let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(range, src) = self;
        let (start_ty, start_aset, start_ct) = range.start.collect_constraints(ctx);
        let (end_ty, end_aset, end_ct) = range.end.collect_constraints(ctx);
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let el_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
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
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(tuple, src) = self;
        let mut aset = AssumptionSet::new();
        let mut cts = vec![];
        let mut tys = vec![];
        for el in tuple.seq.items.iter() {
            let (el_ty, a, ct) = el.collect_constraints(ctx);
            tys.push(el_ty);
            aset.extend(a);
            cts.push(ct);
        }
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let c = EqConstraint::new(ty.clone(), Ty::Tuple(tys)).with_src(src.clone());
        let ct = AttachTree::new(c, NodeTree::new(cts));
        (ty, aset, ct)
    }
}

impl CollectConstraints for (&UnaryOp, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(unop, src) = self;
        let (expr_ty, expr_aset, expr_ct) = unop.expr.collect_constraints(ctx);

        let op_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        ctx.tcx.set_ty(unop.op.id, op_ty.clone());

        let result_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        let name = unop.op.to_string();
        let (fqn, _) = ctx.tcx.lookup_prefix_op(&name).cloned().unwrap();

        log::debug!("unop fqn: {}", fqn);

        let mut aset = expr_aset;
        aset.add(fqn, op_ty.clone());

        let op_src = ctx.srcmap.get(&unop.op);
        let op_ct = ReceiverTree::new(op_ty.to_string());
        let eq = EqConstraint::new(op_ty, Ty::Func(vec![expr_ty], Box::new(result_ty.clone())))
            .with_src(op_src);

        (
            result_ty,
            aset,
            AttachTree::new(eq, NodeTree::new(vec![expr_ct, op_ct])),
        )
    }
}

impl CollectConstraints for (&While, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(while_stmt, _) = self;
        let mut aset = AssumptionSet::new();

        let (cond_ty, cond_aset, cond_tree) = while_stmt.cond.collect_constraints(ctx);
        aset.extend(cond_aset);

        let cond_src = ctx.srcmap.get(&while_stmt.cond);
        let cond_tree = ParentAttachTree::new(
            EqConstraint::new(cond_ty, Ty::bool()).with_src(cond_src),
            cond_tree,
        );

        let (_, body_aset, body_tree) = while_stmt.body.collect_constraints(ctx);
        aset.extend(body_aset);

        let ctree = NodeTree::new(vec![cond_tree, body_tree]);
        (Ty::unit(), aset, ctree)
    }
}
