// DO NOT MODIFY
// This is meant to be a (temporary) reference to the previous type system

use std::{collections::HashSet, ops::Deref};

use ray_shared::{
    pathlib::Path,
    span::{Source, parsed::Parsed},
};
use ray_typing::top::{Predicate, RecvKind, Subst, Substitutable};

use crate::ast::{
    self, BinOp, Block, Boxed, Call, Cast, Curly, CurlyElement, Decl, Dot, Expr, For, If, List,
    Literal, Module, Name, New, Node, Pattern, Range, Ref, Tuple, UnaryOp, While,
};
use crate::bga::{BindingGroup, BindingGroupAnalysis};
use crate::collect::{CollectConstraints, CollectCtx, CollectDeclarations, CollectPatterns};
use ray_typing::{
    assumptions::AssumptionSet,
    constraints::{
        EqConstraint, InstConstraint, ProveConstraint,
        tree::{AttachTree, ConstraintTree, NodeTree, ParentAttachTree, ReceiverTree},
    },
    state::{Env, SchemeEnv, SigmaEnv, TyEnv},
    ty::{ReceiverMode, SigmaTy, Ty, TyScheme, TyVar},
};

impl CollectPatterns for Node<Pattern> {
    fn collect_patterns(&self, ctx: &mut CollectCtx) -> (Ty, TyEnv, ConstraintTree) {
        match &self.value {
            Pattern::Name(n) => n.path.collect_patterns(ctx),
            Pattern::Some(inner) => {
                let (ty, env, ctree) = inner.collect_patterns(ctx);
                ctx.tcx.set_ty(self.id, ty.clone());
                (ty, env, ctree)
            }
            Pattern::Sequence(_) => todo!("collect patterns: {}", self),
            Pattern::Tuple(_) => todo!("collect patterns: {}", self),
            Pattern::Dot(lhs_pat, field_name) => {
                let src = ctx.srcmap.get(self);
                // Collect constraints for the left pattern to obtain its type and env
                let (lhs_ty, env, ctree) = lhs_pat.collect_patterns(ctx);

                // Fresh type variable for the field
                let field_ty = Ty::Var(ctx.tcx.tf().next());

                // Prove that the LHS type has the named field with the given type
                let mut prove = ProveConstraint::new(Predicate::has_field(
                    lhs_ty,
                    field_name.path.name().unwrap().to_string(),
                    field_ty.clone(),
                ));
                prove.info_mut().with_src(src);

                // Set this pattern's type to the field type
                ctx.tcx.set_ty(self.id, field_ty.clone());

                (field_ty, env, AttachTree::new(prove, ctree))
            }
            Pattern::Missing(_) => {
                let ty = Ty::Var(ctx.tcx.tf().next());
                ctx.tcx.set_ty(self.id, ty.clone());
                (ty, TyEnv::new(), ConstraintTree::empty())
            }
            Pattern::Deref(n) => {
                let src = ctx.srcmap.get(self);
                let (ptr_ty, env, ctree) = n.path.collect_patterns(ctx);
                let ty = Ty::Var(ctx.tcx.tf().next());

                log::debug!(
                    "[collect_patterns] Deref({}): ptr_ty={}, ty={}",
                    n,
                    ptr_ty,
                    ty
                );

                // require core::Deref[ptr_ty, ty]
                let deref_trait_fqn = ctx.ncx.builtin_ty("Deref");
                let mut c = ProveConstraint::new(Predicate::class(
                    deref_trait_fqn.to_string(),
                    ptr_ty.clone(),
                    vec![ty.clone()],
                ));
                c.info_mut().with_src(src);
                log::debug!("[collect_patterns] deref predicate = {}", c);

                ctx.tcx.set_ty(self.id, ty.clone());
                (ty, env, AttachTree::new(c, ctree))
            }
        }
    }
}

impl CollectDeclarations for Node<Decl> {
    type Output = Vec<(BindingGroup, SchemeEnv)>;

    fn collect_decls(&self, ctx: &mut CollectCtx) -> Self::Output {
        let src = ctx.srcmap.get(self);
        let (ty_scheme, bg, env) = match &self.value {
            Decl::Extern(ext) => {
                // B = (∅,∅,•) Σ = [x1 :σ,...,xn :σ]
                let mut env = SchemeEnv::new();
                let (fqn, ty_scheme) = match ext.decl() {
                    Decl::Mutable(_, _) => {
                        todo!()
                        // let ty = n.ty.as_deref().unwrap().clone();
                        // let fqn = n.path.clone();
                        // (fqn, ty)
                    }
                    Decl::Name(_, _) => {
                        todo!()
                        // let ty = n.ty.as_deref().unwrap().clone();
                        // let fqn = n.path.clone();
                        // (fqn, ty)
                    }
                    Decl::FnSig(sig) => {
                        let ty = sig.ty.as_ref().unwrap().clone();
                        let fqn = sig.path.value.clone();
                        (fqn, ty)
                    }
                    d @ _ => unreachable!("Decl::Extern: {:?}", d),
                };

                env.insert(fqn, ty_scheme.clone());
                ctx.tcx.set_ty_scheme(self.id, ty_scheme);
                return vec![(BindingGroup::empty().with_src(src.clone()), env)];
            }
            Decl::Func(func) => {
                let func_node = Node {
                    id: self.id,
                    value: func,
                };
                (func_node, &src, None).collect_decls(ctx)
            }
            Decl::Mutable(d) => todo!("collect_decls: Decl::Mutable: {:?}", d),
            Decl::Name(d) => todo!("collect_decls: Decl::Name: {:?}", d),
            Decl::Declare(d) => todo!("collect_decls: Decl::Declare: {:?}", d),
            Decl::FnSig(d) => todo!("collect_decls: Decl::FnSig: {:?}", d),
            Decl::Struct(_) => (
                Ty::unit().into(),
                BindingGroup::empty().with_src(src.clone()),
                Env::new(),
            ),
            Decl::Trait(tr) => {
                let mut env = Env::new();
                for decl in tr.fields.iter() {
                    let sig = variant!(decl.deref(), if Decl::FnSig(f));

                    // store the polymorpphic scheme under a canonical key
                    let raw_key = &sig.path.value;
                    let norm_key = raw_key.with_names_only();
                    log::debug!("trait func: raw={} norm={}", raw_key, norm_key);
                    env.insert(norm_key, sig.ty.clone().unwrap().into());
                }

                (
                    Ty::unit().into(),
                    BindingGroup::empty().with_src(src.clone()),
                    env,
                )
            }
            Decl::TypeAlias(d, _) => todo!("collect_decls: Decl::TypeAlias: {:?}", d),
            Decl::Impl(imp) => {
                let mut decl_pairs = vec![];

                let self_ty = if imp.is_object {
                    imp.ty.deref()
                } else {
                    imp.ty.get_ty_param_at(0).unwrap_or(&Ty::Never)
                };
                if let Some(funcs) = &imp.funcs {
                    for func_node in funcs {
                        let src = ctx.srcmap.get(func_node);
                        // FIXME: static methods can have parameters
                        let self_ty = if func_node.value.sig.params.len() != 0 {
                            Some(self_ty)
                        } else {
                            // a impl function with no parameters is static
                            None
                        };
                        let (fn_ty, fn_bg, fn_env) =
                            (func_node.as_ref(), &src, self_ty).collect_decls(ctx);
                        ctx.tcx.set_ty_scheme(func_node.id, fn_ty);
                        log::debug!("fn_bg = {:?}", fn_bg);
                        log::debug!("fn_env = {:?}", fn_env);

                        // For both inherent and trait impls, we want the
                        // method's declared type scheme available in the
                        // per-module Σ so that binding-group analysis can
                        // Skolemize the method binding just like a free
                        // function. Impl methods are keyed by their fully
                        // qualified impl path, so they do not collide with
                        // the trait's own method declaration.
                        decl_pairs.push((fn_bg, fn_env));
                    }
                }

                if let Some(consts) = &imp.consts {
                    for const_node in consts {
                        let src = ctx.srcmap.get(const_node);
                        let (const_ty, const_bg, const_env) =
                            (&const_node.lhs, const_node.rhs.as_ref(), &src).collect_decls(ctx);

                        ctx.tcx.set_ty(const_node.id, Ty::unit());
                        ctx.tcx.set_ty(const_node.lhs.id, const_ty);
                        log::debug!("const_bg = {:?}", const_bg);
                        log::debug!("const_env = {:?}", const_env);

                        if imp.is_object {
                            // Inherent associated const: expose in Σ
                            decl_pairs.push((const_bg, const_env));
                        } else {
                            // Associated const in a trait impl: do not extend Σ
                            decl_pairs.push((const_bg, Env::new()));
                        }
                    }
                }

                if let Some(ext) = &imp.externs {
                    for (ext_bg, ext_env) in ext.iter().flat_map(|e| e.collect_decls(ctx)) {
                        if imp.is_object {
                            // Inherent externs (e.g., inherent associated fns declared extern)
                            decl_pairs.push((ext_bg, ext_env));
                        } else {
                            // Externs inside trait impls should not pollute Σ
                            decl_pairs.push((ext_bg, Env::new()));
                        }
                    }
                }

                return decl_pairs;
            }
        };

        log::debug!("set type of: {:?}", self);
        ctx.tcx.set_ty_scheme(self.id, ty_scheme);
        vec![(bg, env)]
    }
}

impl CollectDeclarations for (Node<&ast::Func>, &Source, Option<&Ty>) {
    type Output = (TyScheme, BindingGroup, SchemeEnv);

    fn collect_decls(&self, ctx: &mut CollectCtx) -> Self::Output {
        // Collecting constraints for a function is two-fold:
        //   1) (D-FB) Collect constraints for the function binding itself, the LHS (parameter patterns) and RHS (body)
        //   2) (D-TYPE) Collect constraints for the function's type signature, if it exists

        let (func_node, src, _) = self;
        let func = func_node.value;
        let src = (*src).clone();
        let name = &func.sig.path;
        let fn_tv = ctx.tcx.tf().next();
        ctx.tcx.set_ty(func_node.id, Ty::Var(fn_tv.clone()));

        // If annotated and is a function type, expand the param and return types.
        // IMPORTANT: we *instantiate* the function's type scheme here so that any
        // schematic type variables (e.g., `'a`) are replaced by fresh meta
        // variables before we generate equalities. This keeps schema variables
        // out of the global constraint set.
        let (anno_params, anno_ret) = func
            .sig
            .ty
            .as_ref()
            .map(|sig_scheme| {
                if let Ty::Func(params, ret) = sig_scheme.mono() {
                    // Start from the monomorphic view of the function type.
                    let mut func_ty = Ty::Func(params.clone(), Box::new(ret.deref().clone()));

                    // If the scheme is polymorphic, instantiate its quantifiers
                    // to fresh meta variables in the current type context.
                    if !sig_scheme.quantifiers().is_empty() {
                        let mut subst: Subst<TyVar, Ty> = Subst::new();
                        for q in sig_scheme.quantifiers().iter() {
                            let fresh_tv = ctx.tcx.tf().next();
                            subst.insert(q.clone(), Ty::Var(fresh_tv));
                        }
                        func_ty.apply_subst(&subst);
                    }

                    match func_ty {
                        Ty::Func(params, ret) => (params, Some(*ret)),
                        _ => (vec![], None),
                    }
                } else {
                    (vec![], None)
                }
            })
            .unwrap_or_default();

        //
        // D-FB
        //
        // FB: ⟨M⟩,x,A\dom(E),Cl >o [TC1, TC2] ⊢fb lhs = rhs : {|τ1,...,τn,τ|}

        // LHS: x, Union(Ei), [TC1,...,TCn] ⊢lhs x p1 ... pn : {|τ1,...,τn|}
        let insert_mono_ty = |mono_tys: &mut HashSet<TyVar>, ty: &Ty| {
            if let Ty::Var(tv) = ty {
                mono_tys.insert(tv.clone());
            }
        };

        let (fb_aset, fb_env, ctree) = ctx.with_frame(|ctx| {
            let mut mono_tys = ctx.mono_tys.clone();
            let mut param_tys = vec![];
            let mut param_cts = vec![];
            let mut lhs_env = Env::new();
            for (i, param) in func.sig.params.iter().enumerate() {
                let param_name = param.name();
                let (mut param_ty, param_env, mut param_ct) = param_name.collect_patterns(ctx);

                if let Some(anno_param_ty) = anno_params.get(i) {
                    let param_src = ctx.srcmap.get(param);
                    let mut c = EqConstraint::new(param_ty.clone(), anno_param_ty.clone());
                    c.info_mut().with_src(param_src);
                    param_ct = AttachTree::new(c, param_ct);

                    // Now *canonicalize* this param to the annotated type
                    param_ty = anno_param_ty.clone();
                }

                ctx.bound_names.insert(param_name.clone(), param_ty.clone());
                param_tys.push(param_ty.clone());
                param_cts.push(param_ct);
                lhs_env.extend(param_env);
                insert_mono_ty(&mut mono_tys, &param_ty.clone());
                ctx.tcx.set_ty(param.id, param_ty);
            }

            let lhs_ct = NodeTree::new(param_cts);

            // RHS:⟨M + ftv(Cl)⟩,A,TC2 ⊢rhs rhs : τ
            // Canonical return type for this function
            let ret_tv = ctx.tcx.tf().next();
            let ret_ty = Ty::Var(ret_tv.clone());

            let mut rhs_ctx = CollectCtx {
                mono_tys: ctx.mono_tys,
                srcmap: ctx.srcmap,
                tcx: ctx.tcx,
                ncx: ctx.ncx,
                defs: ctx.defs.clone(),
                new_defs: ctx.new_defs,
                bound_names: ctx.bound_names,
                current_ret: Some(ret_ty.clone()),
            };

            let (body_ty, aset, body_ct) = rhs_ctx
                .with_frame(|rhs_ctx| func.body.as_deref().unwrap().collect_constraints(rhs_ctx));

            let (body_ty, body_ct) = if let Some(anno_ret) = anno_ret {
                let body_node = func.body.as_deref().unwrap();
                let body_src = ctx.srcmap.get(body_node);
                let mut c = EqConstraint::new(body_ty.clone(), anno_ret.clone());
                c.info_mut().with_src(body_src);
                (anno_ret, AttachTree::new(c, body_ct))
            } else {
                (body_ty, body_ct)
            };

            let bg = BindingGroup::new(Env::new(), aset, body_ct).with_src(src.clone());
            let sigs = SigmaEnv::new();
            let mut tf = rhs_ctx.tcx.tf();
            let mut bga = BindingGroupAnalysis::new(vec![bg], &sigs, &mut tf, &rhs_ctx.mono_tys);
            let (mut mono_tys, aset, rhs_ct) = bga.analyze();
            drop(tf);

            // combine the mono types with the free variables from the LHS labeled constraint list
            let cl = EqConstraint::lift(&aset, &lhs_env)
                .into_iter()
                .map(|(l, mut c)| {
                    c.info_mut().with_src(src.clone());
                    (l, c)
                })
                .collect::<Vec<_>>();
            mono_tys.extend(cl.iter().map(|(_, c)| c.free_vars()).flatten().cloned());

            let fb_aset = aset - lhs_env.keys();
            let fb_ct = NodeTree::new(vec![lhs_ct, rhs_ct]).spread_list(cl);

            // Constrain the canonical return type to the analyzed body type.
            let mut ret_cs = EqConstraint::new(body_ty.clone(), ret_ty.clone());
            ret_cs.info_mut().with_src(src.clone());

            let fn_ty = Ty::Func(param_tys, Box::new(ret_ty.clone()));
            let mut eq = EqConstraint::new(Ty::Var(fn_tv.clone()), fn_ty);
            eq.info_mut().with_src(src.clone());

            let mut fb_env = Env::new();
            fb_env.insert(name.value.clone(), Ty::Var(fn_tv.clone()));

            let fn_ct = ParentAttachTree::new(ret_cs, fb_ct);

            let ctree = AttachTree::new(
                eq,
                NodeTree::new(vec![ReceiverTree::new(fn_tv.to_string()), fn_ct]),
            );

            (fb_aset, fb_env, ctree)
        });

        //
        // D-TYPE
        //
        // Now that we have the constraints for the function binding
        // we can collect the constraints for the function's type signature.
        // Anchor binding-group level diagnostics (e.g., skolemization errors)
        // to the function *signature* span rather than the full function body,
        // so errors related to the declared type highlight the signature.
        let src = src.respan(func.sig.span);
        let bg = BindingGroup::new(fb_env, fb_aset, ctree).with_src(src);
        let mut sigma = Env::new();
        if let Some(anno_ty) = &func.sig.ty {
            sigma.insert(name.value.clone(), anno_ty.clone());
        }

        (Ty::Var(fn_tv).into(), bg, sigma)
    }
}

impl<'a> CollectConstraints for Module<(), Decl> {
    type Output = ();

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let mut bgroups = vec![];
        let mut defs = Env::new();
        for (bg, decl_env) in self.decls.iter().flat_map(|d| d.collect_decls(ctx)) {
            log::debug!("bg = {:?}", bg);
            log::debug!("decl_env = {:?}", decl_env);
            bgroups.push(bg);
            defs.extend(decl_env);
        }

        let mono_tys = HashSet::new();
        log::debug!("defs: {:?}", defs);
        ctx.defs.extend(defs);

        // DEBUG
        {
            log::debug!("BINDING GROUPS (pre-BGA):");
            for (i, bg) in bgroups.iter().enumerate() {
                // Each bg has an Env for its LHS bindings (fn names, etc.)
                let names: Vec<_> = bg.env.keys().cloned().collect();
                log::debug!("  BG#{i}: {:?}", names);
            }
        }

        let sigs: SigmaEnv = ctx.defs.clone().into();

        let mut tf = ctx.tcx.tf();
        let mut bga = BindingGroupAnalysis::new(bgroups, &sigs, &mut tf, &mono_tys);
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
        if let Expr::TypeAnnotated(_, _) = &self.value {
            todo!()
            // let anno_ty = ty.deref().deref().clone();
            // let (ty, aset, ctree) = ex.collect_constraints(ctx);
            // let mut c1 = SkolConstraint::new(ctx.mono_tys.clone(), ty, anno_ty.clone());
            // c1.info_mut().with_src(src.clone());
            // let b = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
            // let c2 = InstConstraint::new(b.clone(), anno_ty.clone());
            // c2.info_mut().with_src(src.clone());
            // return (
            //     anno_ty,
            //     aset,
            //     AttachTree::new(c2, NodeTree::new(vec![ParentAttachTree::new(c1, ctree)])),
            // );
        }

        let (ty, aset, ct) = match &self.value {
            // Arms in alphabetical order by Expr variant
            Expr::Assign(_) => unreachable!(),
            Expr::BinOp(ex) => (ex, src).collect_constraints(ctx),
            Expr::Block(ex) => (ex, src).collect_constraints(ctx),
            Expr::Boxed(ex) => (ex, src).collect_constraints(ctx),
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
            Expr::Deref(ex) => (ex, src).collect_constraints(ctx),
            Expr::Dot(ex) => (ex, src).collect_constraints(ctx),
            Expr::For(ex) => (ex, src).collect_constraints(ctx),
            Expr::Func(_) => todo!(),
            Expr::If(ex) => (ex, src).collect_constraints(ctx),
            Expr::Index(_) => {
                todo!()
                // (ex, src).collect_constraints(ctx)
            }
            Expr::Labeled(_, _) => todo!(),
            Expr::List(ex) => (ex, src).collect_constraints(ctx),
            Expr::Literal(ex) => (ex, src).collect_constraints(ctx),
            Expr::Loop(_) => todo!(),
            Expr::Missing(_) => todo!(),
            Expr::Name(ex) => (ex, src).collect_constraints(ctx),
            Expr::New(ex) => (ex, src).collect_constraints(ctx),
            Expr::NilCoalesce(_) => todo!("old_collect: NilCoalesce"),
            Expr::Paren(ex) => (ex, src).collect_constraints(ctx),
            Expr::Path(ex) => (ex, src).collect_constraints(ctx),
            Expr::Pattern(ex) => (ex, src).collect_constraints(ctx),
            Expr::Range(ex) => (ex, src).collect_constraints(ctx),
            Expr::Ref(ex) => (ex, src).collect_constraints(ctx),
            Expr::Return(ret) => {
                if let Some(ex) = ret {
                    let ex_src = &ctx.srcmap.get(ex);
                    let (ex_ty, aset, ct) = (ex, ex_src).collect_constraints(ctx);
                    // If we are inside a function, constrain the returned
                    // expression type to the function's canonical return type.
                    if let Some(ret_ty) = ctx.current_ret.clone() {
                        let mut c = EqConstraint::new(ex_ty.clone(), ret_ty.clone());
                        c.info_mut().with_src(ex_src.clone());
                        let ct = AttachTree::new(c, ct);
                        (ex_ty, aset, ct)
                    } else {
                        (ex_ty, aset, ct)
                    }
                } else {
                    (Ty::unit(), AssumptionSet::new(), ConstraintTree::empty())
                }
            }
            Expr::Sequence(_) => todo!(),
            Expr::Some(inner) => {
                let (inner_ty, aset, ct) = inner.collect_constraints(ctx);
                (Ty::nilable(inner_ty), aset, ct)
            }
            Expr::Tuple(ex) => (ex, src).collect_constraints(ctx),
            Expr::Type(ty) => (ty, src).collect_constraints(ctx),
            Expr::TypeAnnotated(_, _) => {
                unreachable!("handled above")
            }
            Expr::UnaryOp(ex) => (ex, src).collect_constraints(ctx),
            Expr::Unsafe(_) => todo!(),
            Expr::While(ex) => (ex, src).collect_constraints(ctx),
        };

        ctx.tcx.set_ty(self.id, ty.clone());
        (ty, aset, ct)
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

        // Operator token type
        let op_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        ctx.tcx.set_ty(binop.op.id, op_ty.clone());

        // Result type of the binary expression
        let result_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        // Resolve operator symbol to FQN and its backing trait
        let name = binop.op.to_string();

        let fqn = match ctx.tcx.lookup_infix_op(&name).cloned() {
            Some((fqn, _)) => fqn,
            _ => Path::from(name), // fallback to `name`
        };

        log::debug!("binop fqn: {}", fqn);

        // Assumptions: we "have" the operator value with type op_ty under its normalized key,
        // so Σ lookup during InstConstraint lifting will match
        let mut aset = lhs_aset;
        let norm_fqn = fqn.with_names_only();
        aset.add(norm_fqn.clone(), op_ty.clone());
        aset.extend(rhs_aset);
        let op_src = ctx.srcmap.get(&binop.op);
        let op_ct = ReceiverTree::new(op_ty.to_string());
        let mut eq_op = EqConstraint::new(
            op_ty.clone(),
            Ty::Func(
                vec![lhs_ty.clone(), rhs_ty.clone()],
                Box::new(result_ty.clone()),
            ),
        );
        eq_op.info_mut().with_src(op_src.clone());

        let ct = AttachTree::list(vec![eq_op], NodeTree::new(vec![lhs_ct, op_ct, rhs_ct]));
        (result_ty, aset, ct)
    }
}

impl CollectConstraints for (&Block, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        ctx.with_frame(|ctx| {
            let &(block, src) = self;
            let mut block_ty = Ty::unit();
            let mut bgs = vec![];
            let mut mono_tys = ctx.mono_tys.clone();
            for stmt in block.stmts.iter() {
                let src = ctx.srcmap.get(stmt);
                let bg = if let Expr::Assign(assign) = &stmt.value {
                    // Special case: place assignments (field or deref), which do not introduce
                    // new bindings and should reuse existing types.
                    let (lhs_ty, bg) =
                        if matches!(assign.lhs.value, Pattern::Dot(..) | Pattern::Deref(..)) {
                            // Collect constraints for LHS place and RHS value, then equate their types.
                            let (lhs_ty, lhs_aset, lhs_ct) =
                                (&assign.lhs.value, &src).collect_constraints(ctx);
                            let (rhs_ty, rhs_aset, rhs_ct) =
                                assign.rhs.as_ref().collect_constraints(ctx);

                            let mut eq = EqConstraint::new(lhs_ty.clone(), rhs_ty);
                            eq.info_mut().with_src(src.clone());

                            let mut aset = lhs_aset;
                            aset.extend(rhs_aset);
                            let ctree = AttachTree::new(eq, NodeTree::new(vec![lhs_ct, rhs_ct]));

                            if let Ty::Var(tv) = &lhs_ty {
                                mono_tys.insert(tv.clone());
                            }

                            // No new names are introduced by a place assignment; env is empty.
                            (
                                lhs_ty,
                                BindingGroup::new(TyEnv::new(), aset, ctree).with_src(src),
                            )
                        } else {
                            // Default: use declaration collection (patterns may bind names).
                            let (lhs_ty, bg, _) =
                                (&assign.lhs, assign.rhs.as_ref(), &src).collect_decls(ctx);

                            // Seed `bound_names` with any new bindings introduced by this
                            // assignment. This ensures that subsequent uses of these names
                            // in place contexts (e.g., `*x`, `x.f`) see the same type
                            // variable, and also implements the "rebind with new type"
                            // semantics by overwriting any previous entry.
                            for (path, ty) in bg.env.iter() {
                                ctx.bound_names.insert(path.clone(), ty.clone());
                            }

                            if let Ty::Var(tv) = &lhs_ty {
                                mono_tys.insert(tv.clone());
                            }

                            (lhs_ty, bg)
                        };

                    ctx.tcx.set_ty(stmt.id, Ty::unit());
                    ctx.tcx.set_ty(assign.lhs.id, lhs_ty);
                    bg
                } else {
                    // since this is a non-assignment expression we need to
                    // collect the constraints and create a binding group
                    let (expr_ty, aset, ctree) = stmt.collect_constraints(ctx);
                    if let Ty::Var(tv) = &expr_ty {
                        mono_tys.insert(tv.clone());
                    }

                    // note that the environment of the binding group is empty
                    // because there is no "LHS" of the expression
                    let bg = BindingGroup::new(TyEnv::new(), aset, ctree).with_src(src);
                    block_ty = expr_ty;
                    bg
                };

                bgs.push(bg);
            }

            // now that the binding groups are collected, we can analyze them
            let defs = ctx.defs.clone().into();
            let mut tf = ctx.tcx.tf();
            let mut bga = BindingGroupAnalysis::new(bgs, &defs, &mut tf, &mono_tys);
            let (_, aset, ctree) = bga.analyze();
            log::debug!("ty = {}", block_ty);
            log::debug!("aset = {:?}", aset);

            let var = Ty::Var(tf.with_scope(&src.path));
            let mut eq = EqConstraint::new(var.clone(), block_ty.clone());
            eq.info_mut().with_src(src.clone());
            (block_ty, aset, AttachTree::new(eq, ctree))
        })
    }
}

impl CollectConstraints for (&Boxed, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(boxed, src) = self;
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        let (inner_ty, aset, ct) = boxed.inner.collect_constraints(ctx);
        let mut c = EqConstraint::new(ty.clone(), Ty::refty(inner_ty));
        c.info_mut().with_src(src.clone());

        (ty, aset, AttachTree::new(c, ct))
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

        let (lhs_ty, ct1) = if let Expr::Dot(dot) = &call.callee.value {
            // Collect constraints for the receiver expression.
            let (recv_ty, recv_aset, mut ct1) = dot.lhs.collect_constraints(ctx);
            aset.extend(recv_aset);

            // Fresh type for the method value.
            let lhs_src = ctx.srcmap.get(&dot.lhs);
            let field_ty = Ty::Var(ctx.tcx.tf().with_scope(&lhs_src.path));
            log::debug!("rhs: {}", dot.rhs.path);
            let method_name = dot.rhs.path.name().unwrap().to_string();
            let recv_param_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
            if let Some((trait_ty, resolved_method)) = ctx.tcx.resolve_trait_method(&method_name) {
                // For non-static receiver methods, introduce a fresh receiver-parameter type and
                // a Recv predicate tying the receiver expression type to that parameter type.
                let recv_mode = resolved_method.recv_mode;
                let fqn = if !matches!(recv_mode, ReceiverMode::None) {
                    let fqn = trait_ty.create_method_path(&method_name, Some(&recv_param_ty));
                    let recv_kind = match recv_mode {
                        ReceiverMode::Value => RecvKind::Value,
                        ReceiverMode::Ptr => RecvKind::Ref,
                        ReceiverMode::None => unreachable!(),
                    };

                    let mut prove = ProveConstraint::new(Predicate::recv(
                        recv_kind,
                        recv_ty.clone(),
                        recv_param_ty.clone(),
                    ));
                    prove.info_mut().with_src(lhs_src.clone());
                    ct1 = AttachTree::new(prove, ct1);

                    // Receiver parameter is the first argument to the method.
                    arg_tys.push(recv_param_ty);
                    fqn
                } else {
                    trait_ty.create_method_path(&method_name, Some(&recv_ty))
                };

                log::debug!("[Call::collect_constraints] fqn: {}", fqn);

                // Add the normalized key to the assumption set so Σ lookup can find the scheme.
                let norm_fqn = fqn.with_names_only();
                log::debug!("Call::Dot adding normalized fqn: {}", norm_fqn);
                aset.add(norm_fqn.clone(), field_ty.clone());

                // Record the type of the callee expression as the method's function type.
                ct1 = NodeTree::new(vec![ReceiverTree::new(field_ty.to_string()), ct1]);
                ctx.tcx.set_ty(call.callee.id, field_ty.clone());
                ctx.tcx
                    .set_call_resolution(call.call_resolution_id(), fqn.clone());
                (field_ty, ct1)
            } else {
                // we failed to lookup the method, so we have to return something here
                (Ty::Never, ConstraintTree::empty())
            }
        } else {
            let (lhs_ty, fun_aset, ct1) = call.callee.collect_constraints(ctx);
            log::debug!("type of {}: {}", call.callee, lhs_ty);
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
        let rhs_ty = Ty::Func(arg_tys, Box::new(ret_ty.clone()));

        log::debug!("creating eq constraint: {} == {}", lhs_ty, rhs_ty);
        let mut c = EqConstraint::new(lhs_ty, rhs_ty);
        c.info_mut().with_src(src.clone());

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
        let mut c = EqConstraint::new(v.clone(), cast.ty.deref().clone());
        c.info_mut().with_src(src.clone());
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
        let mut c1 = InstConstraint::new(ty.clone(), SigmaTy::scheme(curly.ty.clone()));
        c1.info_mut().with_src(src.clone());
        let mut cts = vec![AttachTree::new(c1, ConstraintTree::empty())];
        let mut aset = AssumptionSet::new();
        for el in curly.elements.iter() {
            let (name, (field_ty, a, ct)) = match &el.value {
                CurlyElement::Labeled(name, field) => (name, field.collect_constraints(ctx)),
                _ => unreachable!("all elements should be labeled at this point"),
            };
            aset.extend(a);
            let mut prove = ProveConstraint::new(Predicate::has_field(
                ty.clone(),
                name.path.name().unwrap().to_string(),
                field_ty.clone(),
            ));
            prove.info_mut().with_src(src.clone());
            cts.push(AttachTree::new(prove, ct));
            ctx.tcx.set_ty(el.id, field_ty);
        }

        log::debug!("curly ty: {}", curly.ty);

        let ty_args = (0..curly.ty.free_vars().len())
            .into_iter()
            .map(|_| Ty::Var(ctx.tcx.tf().with_scope(&src.path)))
            .collect::<Vec<_>>();

        let fqn = curly.lhs.as_ref().unwrap().to_string();
        let mut c2 = EqConstraint::new(ty.clone(), Ty::with_tys(&fqn, ty_args));
        c2.info_mut().with_src(src.clone());

        let ct = AttachTree::new(c2, NodeTree::new(cts));

        (ty, aset, ct)
    }
}

impl CollectConstraints for (&ast::Deref, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(deref, src) = self;

        // result ty of *expr
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        // receiver type for Deref
        let ptr_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        let (expr_ty, aset, ct) = deref.expr.collect_constraints(ctx);

        // expr_ty == ptr_ty
        let mut eq = EqConstraint::new(expr_ty, ptr_ty.clone());
        eq.info_mut().with_src(src.clone());

        // require Deref[ptr_ty, ty]
        let deref_trait_fqn = ctx.ncx.builtin_ty("Deref");
        let mut prove = ProveConstraint::new(Predicate::class(
            deref_trait_fqn.to_string(),
            ptr_ty.clone(),
            vec![ty.clone()],
        ));
        prove.info_mut().with_src(src.clone());

        let ct = AttachTree::new(eq, AttachTree::new(prove, ct));
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
        let field_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        let mut prove = ProveConstraint::new(Predicate::has_field(
            lhs_ty,
            dot.rhs.path.name().unwrap().to_string(),
            field_ty.clone(),
        ));
        prove.info_mut().with_src(src.clone());
        (field_ty, aset, AttachTree::new(prove, ct))
    }
}

impl CollectConstraints for (&ast::Func, &Source) {
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

        // Special handling for `if some(pat) = expr { ... }`:
        // treat the condition as a pattern match on a `nilable` value, binding
        // the inner pattern only in the then-branch.
        let (cond_ty, cond_aset, cond_ct, then_env) =
            if let Expr::Assign(assign) = &if_ex.cond.value {
                if let Pattern::Some(_) = assign.lhs.value {
                    let cond_src = ctx.srcmap.get(&if_ex.cond);

                    // Collect pattern bindings and constraints for the LHS pattern.
                    let (inner_ty, env, pat_ct) = assign.lhs.collect_patterns(ctx);

                    // Collect constraints for the RHS expression.
                    let (rhs_ty, rhs_aset, rhs_ct) = assign.rhs.as_ref().collect_constraints(ctx);

                    // Constrain the RHS to be `nilable[inner_ty]`.
                    let mut eq_nil = EqConstraint::new(rhs_ty, Ty::nilable(inner_ty.clone()));
                    eq_nil.info_mut().with_src(cond_src.clone());

                    let cond_ct = AttachTree::new(eq_nil, NodeTree::new(vec![pat_ct, rhs_ct]));

                    // The overall condition has boolean type.
                    let cond_ty = Ty::bool();
                    ctx.tcx.set_ty(if_ex.cond.id, cond_ty.clone());

                    (cond_ty, rhs_aset, cond_ct, Some(env))
                } else {
                    // Fallback to the regular boolean condition logic.
                    let (cond_ty, cond_aset, cond_ct) = if_ex.cond.collect_constraints(ctx);
                    (cond_ty, cond_aset, cond_ct, None)
                }
            } else {
                let (cond_ty, cond_aset, cond_ct) = if_ex.cond.collect_constraints(ctx);
                (cond_ty, cond_aset, cond_ct, None)
            };

        aset.extend(cond_aset);

        let cond_src = ctx.srcmap.get(&if_ex.cond);
        let mut eq = EqConstraint::new(cond_ty, Ty::bool());
        eq.info_mut().with_src(cond_src);
        cts.push(ParentAttachTree::new(eq, cond_ct));

        let (then_ty, then_aset, then_ct) = ctx.with_frame(|ctx| {
            if let Some(env) = then_env.as_ref() {
                for (path, ty) in env.iter() {
                    ctx.bound_names.insert(path.clone(), ty.clone());
                }
            }
            if_ex.then.collect_constraints(ctx)
        });
        aset.extend(then_aset);
        log::debug!("then_ty = {}", then_ty);

        let then_src = ctx.srcmap.get(&if_ex.then);
        if let Some(els) = if_ex.els.as_deref() {
            let (else_ty, else_aset, else_ct) = ctx.with_frame(|ctx| els.collect_constraints(ctx));
            let else_src = ctx.srcmap.get(els);
            aset.extend(else_aset);
            log::debug!("else_ty = {}", else_ty);

            let mut then_eq = EqConstraint::new(then_ty, ty.clone());
            then_eq.info_mut().with_src(then_src);
            cts.push(ParentAttachTree::new(then_eq, then_ct));

            let mut else_eq = EqConstraint::new(else_ty, ty.clone());
            else_eq.info_mut().with_src(else_src);
            cts.push(ParentAttachTree::new(else_eq, else_ct));
        } else {
            // Without an else-branch, treat the `if` expression as having the
            // same type as its then-branch (statement-like `if`).
            let mut then_eq = EqConstraint::new(then_ty, ty.clone());
            then_eq.info_mut().with_src(then_src);
            cts.push(ParentAttachTree::new(then_eq, then_ct));
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
            let mut c = EqConstraint::new(el_ty.clone(), item_ty);
            c.info_mut().with_src(src.clone());
            cts.push(ParentAttachTree::new(c, item_ct));
            aset.extend(item_aset);
        }

        let norm_list_fqn = ctx.ncx.builtin_ty("list").with_names_only();
        log::debug!("[collect_contraints] norm_list_fqn = {}", norm_list_fqn);
        let list_ty = Ty::proj(Ty::con(norm_list_fqn), vec![el_ty]);
        let mut c = EqConstraint::new(ty.clone(), list_ty);
        c.info_mut().with_src(src.clone());
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
                if let Some(size) = size {
                    let sign = if !signed { "u" } else { "i" };
                    let ty = if *size != 0 {
                        format!("{}{}", sign, size)
                    } else {
                        format!("{}int", sign)
                    };
                    Ty::con(ty)
                } else {
                    let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
                    let int_trait_fqn = ctx.ncx.builtin_ty("Int");
                    log::debug!("int_trait_fqn = {}", int_trait_fqn);
                    let mut prove = ProveConstraint::new(Predicate::class(
                        int_trait_fqn.to_string(),
                        t.clone(),
                        vec![],
                    ));
                    prove.info_mut().with_src(src.clone());
                    ctree = AttachTree::list(vec![prove], ctree);
                    t
                }
            }
            Literal::Float { size, .. } => {
                if *size != 0 {
                    Ty::con(format!("f{}", size))
                } else {
                    let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
                    let float_trait_fqn = ctx.ncx.builtin_ty("Float");
                    let mut prove = ProveConstraint::new(Predicate::class(
                        float_trait_fqn.to_string(),
                        t.clone(),
                        vec![],
                    ));
                    prove.info_mut().with_src(src.clone());
                    ctree = AttachTree::list(vec![prove], ctree);
                    t
                }
            }
            Literal::String(_) => Ty::string(),
            Literal::ByteString(_) => Ty::bytes(),
            Literal::Byte(_) => Ty::u8(),
            Literal::Char(_) => Ty::char(),
            Literal::Bool(_) => Ty::bool(),
            Literal::Nil => {
                // Give `nil` a polymorphic nilable type: nilable[β] for a fresh β.
                let t = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
                Ty::nilable(t)
            }
            Literal::Unit => Ty::unit(),
            Literal::UnicodeEscSeq(_) => unimplemented!("unicode escape sequence"),
        };

        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));
        log::debug!("ty = {}", ty);
        log::debug!("literal_ty = {}", literal_ty);
        let mut c = EqConstraint::new(ty.clone(), literal_ty);
        c.info_mut().with_src(src.clone());
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
        let ty = if let Some(existing_ty) = ctx.bound_names.get(&name.path) {
            log::debug!(
                "[Name::collect_constraints] hit bound_names path={} -> {}",
                name.path,
                existing_ty
            );
            existing_ty.clone()
        } else {
            log::debug!(
                "[Name::collect_constraints] MISS path={} (creating fresh)",
                name.path
            );
            Ty::Var(ctx.tcx.tf().with_scope(&src.path))
        };

        let label = ty.to_string();
        let mut aset = AssumptionSet::new();
        aset.add(name.path.clone(), ty.clone());
        (ty, aset, ReceiverTree::new(label))
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
            let mut c = EqConstraint::new(count_ty, Ty::uint());
            c.info_mut().with_src(count_src);
            log::debug!("count constraint: {:?}", c);
            log::debug!("count ctree: {:#?}", count_ct);
            aset.extend(count_aset);
            cs.push(c);
            cts.push(count_ct)
        }

        cs.push(EqConstraint::new(
            result_ty.clone(),
            Ty::Ref(Box::new(pointee_ty)),
        ));

        (result_ty, aset, AttachTree::list(cs, NodeTree::new(cts)))
    }
}

/// Helpers for typing lvalue "places" (names, derefs, field accesses) in
/// assignment and pattern contexts. These do not introduce new bindings in
/// `bound_names`; they only reuse existing bindings and emit constraints
/// describing how the place relates to its base expression.
fn collect_pattern_name(
    name: &Name,
    src: &Source,
    ctx: &mut CollectCtx,
) -> (Ty, AssumptionSet, ConstraintTree) {
    let ty = if let Some(existing) = ctx.bound_names.get(&name.path) {
        existing.clone()
    } else {
        debug_assert!(
            false,
            "collect_pattern_name: unbound place name {} at {}",
            name.path, src.path
        );
        Ty::Var(ctx.tcx.tf().with_scope(&src.path))
    };

    let label = ty.to_string();
    let mut aset = AssumptionSet::new();
    aset.add(name.path.clone(), ty.clone());
    let ctree = ReceiverTree::new(label);
    (ty, aset, ctree)
}

fn collect_pattern_deref(
    name: &Name,
    src: &Source,
    ctx: &mut CollectCtx,
) -> (Ty, Ty, AssumptionSet, ConstraintTree) {
    // `*name`: `name` has pointer-ish type `ptr_ty`, constrained by core::Deref,
    // and the place type is the pointee `inner_ty`.
    let ptr_ty = if let Some(existing) = ctx.bound_names.get(&name.path) {
        existing.clone()
    } else {
        debug_assert!(
            false,
            "collect_pattern_deref: unbound place name {} at {}",
            name.path, src.path
        );
        Ty::Var(ctx.tcx.tf().with_scope(&src.path))
    };
    let inner_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

    let deref_trait_fqn = ctx.ncx.builtin_ty("Deref");
    let mut aset = AssumptionSet::new();
    aset.add(name.path.clone(), ptr_ty.clone());

    let mut prove = ProveConstraint::new(Predicate::class(
        deref_trait_fqn.to_string(),
        ptr_ty.clone(),
        vec![inner_ty.clone()],
    ));
    prove.info_mut().with_src(src.clone());

    let ctree = AttachTree::new(prove, ReceiverTree::new(ptr_ty.to_string()));
    (ptr_ty, inner_ty, aset, ctree)
}

fn collect_pattern_dot(
    lhs_pat: &Node<Pattern>,
    field_name: &Name,
    src: &Source,
    ctx: &mut CollectCtx,
) -> (Ty, AssumptionSet, ConstraintTree) {
    // `lhs.field`: the place type is the field type, and we prove a has_field
    // predicate relating the base record type to the field type.
    let lhs_src = ctx.srcmap.get(lhs_pat);
    let (lhs_ty, aset, ctree) = (&lhs_pat.value, &lhs_src).collect_constraints(ctx);

    // Record the type of the base pattern node so later passes (LIR gen) can query it by id.
    ctx.tcx.set_ty(lhs_pat.id, lhs_ty.clone());

    // Fresh type variable for the field
    let field_ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

    // Prove the has_field predicate tying the base type to the field type
    let mut prove = ProveConstraint::new(Predicate::has_field(
        lhs_ty,
        field_name.path.name().unwrap().to_string(),
        field_ty.clone(),
    ));
    prove.info_mut().with_src(src.clone());

    (field_ty, aset, AttachTree::new(prove, ctree))
}

impl CollectConstraints for (&Pattern, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(pattern, src) = self;
        match pattern {
            Pattern::Name(name) => collect_pattern_name(name, src, ctx),
            Pattern::Deref(Node { id: _, value: name }) => {
                let (_ptr_ty, inner_ty, aset, ctree) = collect_pattern_deref(name, src, ctx);
                (inner_ty, aset, ctree)
            }
            Pattern::Dot(lhs_pat, field_name) => collect_pattern_dot(lhs_pat, field_name, src, ctx),
            Pattern::Some(inner) => {
                // `some(pat)` as a pattern doesn’t itself introduce a new
                // type; we treat it as having the same type as its inner
                // pattern, and rely on the surrounding context (e.g., an
                // assignment or if-condition) to constrain the matched
                // expression to `nilable[inner_ty]`.
                (&inner.value, src).collect_constraints(ctx)
            }
            Pattern::Sequence(_) => todo!(),
            Pattern::Tuple(_) => todo!(),
            Pattern::Missing(_) => todo!(),
        }
    }
}

impl CollectConstraints for (&Parsed<TyScheme>, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(ty_scheme, src) = self;
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        let mut eq = EqConstraint::new(ty.clone(), Ty::ty_type(ty_scheme.mono().clone()));
        eq.info_mut().with_src(src.clone());

        (
            ty,
            AssumptionSet::new(),
            AttachTree::new(eq, ConstraintTree::empty()),
        )
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
        let ty = if let Some(existing_ty) = ctx.bound_names.get(&path) {
            log::debug!(
                "[Path::collect_constraints] hit bound_names path={} -> {}",
                path,
                existing_ty
            );
            existing_ty.clone()
        } else {
            log::debug!(
                "[Path::collect_constraints] MISS path={} (creating fresh)",
                path
            );
            Ty::Var(ctx.tcx.tf().with_scope(&src.path))
        };
        let label = ty.to_string();
        let mut aset = AssumptionSet::new();
        aset.add(path.clone(), ty.clone());
        (ty, aset, ReceiverTree::new(label))
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
        let mut range_eq = EqConstraint::new(ty.clone(), Ty::range(el_ty.clone()));
        range_eq.info_mut().with_src(src.clone());
        let mut start_eq = EqConstraint::new(el_ty.clone(), start_ty);
        start_eq.info_mut().with_src(src.clone());
        let mut end_eq = EqConstraint::new(el_ty.clone(), end_ty);
        end_eq.info_mut().with_src(src.clone());

        let ct = AttachTree::new(
            range_eq,
            NodeTree::new(vec![
                ParentAttachTree::new(start_eq, start_ct),
                ParentAttachTree::new(end_eq, end_ct),
            ]),
        );

        let mut aset = AssumptionSet::new();
        aset.extend(start_aset);
        aset.extend(end_aset);

        (ty, aset, ct)
    }
}

impl CollectConstraints for (&Ref, &Source) {
    type Output = Ty;

    fn collect_constraints(
        &self,
        ctx: &mut CollectCtx,
    ) -> (Self::Output, AssumptionSet, ConstraintTree) {
        let &(rf, src) = self;
        let ty = Ty::Var(ctx.tcx.tf().with_scope(&src.path));

        let (el_ty, aset, ct) = rf.expr.collect_constraints(ctx);
        let mut eq = EqConstraint::new(ty.clone(), Ty::refty(el_ty.clone()));
        eq.info_mut().with_src(src.clone());

        (ty, aset, AttachTree::new(eq, ct))
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
        let mut c = EqConstraint::new(ty.clone(), Ty::Tuple(tys));
        c.info_mut().with_src(src.clone());
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
        let norm_fqn = fqn.with_names_only();
        aset.add(norm_fqn, op_ty.clone());

        let op_src = ctx.srcmap.get(&unop.op);
        let op_ct = ReceiverTree::new(op_ty.to_string());
        let mut eq = EqConstraint::new(op_ty, Ty::Func(vec![expr_ty], Box::new(result_ty.clone())));
        eq.info_mut().with_src(op_src);
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
        let mut eq = EqConstraint::new(cond_ty, Ty::bool());
        eq.info_mut().with_src(cond_src);
        let cond_tree = ParentAttachTree::new(eq, cond_tree);

        let (_, body_aset, body_tree) =
            ctx.with_frame(|ctx| while_stmt.body.collect_constraints(ctx));
        aset.extend(body_aset);

        let ctree = NodeTree::new(vec![cond_tree, body_tree]);
        (Ty::unit(), aset, ctree)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use ray_shared::pathlib::Path;
    use ray_typing::{
        bound_names::BoundNames,
        constraints::tree::BottomUpWalk,
        state::{Env, SchemeEnv},
    };

    use crate::{
        collect::{CollectConstraints, CollectCtx},
        errors::RayError,
        sema::ModuleBuilder,
    };

    #[test]
    fn test_collect_function() -> Result<(), Vec<RayError>> {
        let src = r#"
        fn foo(x: int) -> int {
            x + 1
        }
        "#;
        let mut result = ModuleBuilder::from_src(&src, Path::from("#test"))?;
        result.tcx.add_infix_op(
            "+".into(),
            Path::from("core::Add::+"),
            Path::from("core::Add"),
        );

        let mono_tys = HashSet::new();
        let mut new_defs = Env::new();
        let mut ctx = CollectCtx {
            mono_tys: &mono_tys,
            srcmap: &result.srcmap,
            tcx: &mut result.tcx,
            ncx: &mut result.ncx,
            defs: SchemeEnv::new(),
            new_defs: &mut new_defs,
            bound_names: &mut BoundNames::new(),
            current_ret: None,
        };
        let (_, _, c) = result.module.collect_constraints(&mut ctx);
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        println!("tcx = {:#?}", result.tcx);
        println!("ncx = {:#?}", result.ncx);
        for c in constraints {
            println!("{}", c);
        }

        Ok(())
    }
}
