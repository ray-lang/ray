use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap, HashSet},
    rc::Rc,
};

use itertools::Itertools as _;
use ray_core::{ast::Node, convert::ToSet};
use ray_lir::{self as lir, NamedInst};
use ray_shared::{
    pathlib::{ItemPath, Path},
    ty::{Ty, TyVar},
    utils::join,
};
use ray_typing::{
    constraints::{ClassPredicate, Predicate},
    context::MetaAllocator,
    impl_match::{instantiate_impl_predicates, match_impl_head},
    types::{ImplTy, Subst, Substitutable, TyScheme},
    unify::{match_scheme_vars, mgu},
};

use crate::mangle;

#[derive(Debug)]
enum PolyValue<'a> {
    Call(&'a mut lir::Call),
    FuncRef(&'a mut lir::FuncRef),
}

#[derive(Debug)]
struct PolyRef<'a> {
    value: PolyValue<'a>,
    poly_ty: TyScheme,   // the polymorphic type
    callee_ty: TyScheme, // the type of the callee (which may be polymorphic as well)
}

struct MonoMetaAllocator {
    next_meta_id: u32,
    reusable_metas: Vec<TyVar>,
}

impl MonoMetaAllocator {
    fn new() -> Self {
        MonoMetaAllocator {
            next_meta_id: 0,
            reusable_metas: Vec::new(),
        }
    }
}

impl MetaAllocator for MonoMetaAllocator {
    fn fresh_meta(&mut self) -> Ty {
        if let Some(meta) = self.reusable_metas.pop() {
            return Ty::Var(meta);
        }

        let id = self.next_meta_id;
        self.next_meta_id += 1;

        let mut path = Path::new();
        path.append_mut(format!("?tm{}", id));
        Ty::Var(TyVar::new(path))
    }

    fn reuse_metas(&mut self, metas: Vec<TyVar>) {
        self.reusable_metas.extend(metas);
    }
}

#[derive(Debug)]
pub struct Monomorphizer<'p> {
    program: Rc<RefCell<&'p mut lir::Program>>,
    extern_set: HashSet<Path>,
    name_set: HashSet<Path>,
    poly_fn_map: HashMap<Path, Vec<lir::Func>>, // polymorphic functions (multiple impls per key)
    impls_by_trait: BTreeMap<ItemPath, Vec<ImplTy>>,
    trait_member_set: HashSet<Path>,
    poly_mono_fn_idx: HashMap<Path, Vec<(Path, Ty)>>, // a mapping of polymorphic functions to monomorphizations
    mono_poly_fn_idx: HashMap<Path, Path>, // a mapping of monomorphic functions to their polymorphic counterpart
}

impl<'p> Monomorphizer<'p> {
    pub fn new(program: &'p mut lir::Program) -> Monomorphizer<'p> {
        // TODO: don't clone these into the Monomorphizer (reference them outside)
        let poly_fn_map: HashMap<Path, Vec<lir::Func>> = program
            .poly_fn_map
            .iter()
            .map(|(name, indices)| {
                let funcs: Vec<lir::Func> = indices
                    .iter()
                    .map(|&i| program.funcs[i].clone())
                    .collect();
                (name.clone(), funcs)
            })
            .collect();

        let name_set = program.funcs.iter().map(|f| f.name.clone()).collect();
        log::debug!("[monomorphize] name set: {:#?}", name_set);
        let extern_set = program
            .extern_map
            .keys()
            .map(|p| p.with_names_only())
            .to_set();
        log::debug!("[monomorphize] extern set: {:#?}", extern_set);
        let trait_member_set = program.trait_member_set.clone();
        log::debug!("[monomorphize] trait_member_set: {:#?}", trait_member_set);
        let impls_by_trait = program.impls_by_trait.clone();
        Monomorphizer {
            program: Rc::new(RefCell::new(program)),
            poly_fn_map,
            name_set,
            extern_set,
            impls_by_trait,
            trait_member_set,
            poly_mono_fn_idx: HashMap::new(),
            mono_poly_fn_idx: HashMap::new(),
        }
    }

    fn candidate_is_applicable(&self, cand_ty: &TyScheme, subst: &Subst) -> Option<Vec<Predicate>> {
        if cand_ty.qualifiers.is_empty() {
            return None;
        }

        let mut preds = cand_ty.qualifiers.clone();
        preds.apply_subst(subst);

        let mut meta_alloc = MonoMetaAllocator::new();
        let mut visiting = HashSet::new();
        if self.check_predicates(&preds, subst, &mut meta_alloc, &mut visiting) {
            None
        } else {
            Some(preds)
        }
    }

    fn check_predicates(
        &self,
        preds: &[Predicate],
        subst: &Subst,
        meta_alloc: &mut MonoMetaAllocator,
        visiting: &mut HashSet<ClassPredicate>,
    ) -> bool {
        for pred in preds {
            let Predicate::Class(class_pred) = pred else {
                continue;
            };

            // Only reject if the predicate is ground; if it's still polymorphic
            // after substitution, we can't decide here.
            if !class_pred.is_ground() {
                continue;
            }

            if visiting.contains(class_pred) {
                continue;
            }

            visiting.insert(class_pred.clone());
            let ok = self.check_class_predicate(class_pred, subst, meta_alloc, visiting);
            visiting.remove(class_pred);
            if !ok {
                return false;
            }
        }

        true
    }

    fn check_class_predicate(
        &self,
        pred: &ClassPredicate,
        subst: &Subst,
        meta_alloc: &mut MonoMetaAllocator,
        visiting: &mut HashSet<ClassPredicate>,
    ) -> bool {
        for impl_ty in self.impls_by_trait.get(&pred.path).into_iter().flatten() {
            let Some(head) = match_impl_head(pred, impl_ty, subst, meta_alloc, &Default::default())
            else {
                log::debug!(
                    "[check_class_predicate] could not match predicate {} with impl: {:?}",
                    pred,
                    impl_ty
                );
                continue;
            };

            log::debug!("[check_class_predicate] impl match = {:?}", head);
            let preds = instantiate_impl_predicates(impl_ty, &head.schema_subst, &head.trial_subst);
            if self.check_predicates(&preds, &head.trial_subst, meta_alloc, visiting) {
                meta_alloc.reuse_metas(head.trial_metas);
                return true;
            }

            log::debug!(
                "[check_class_predicate] child predicates failed impl check: predicates = [{}]",
                join(&preds, ", ")
            );
            meta_alloc.reuse_metas(head.trial_metas);
        }

        false
    }

    fn add_mono_fn_mapping(&mut self, poly_name: &Path, mono_name: &Path, mono_ty: Ty) {
        self.poly_mono_fn_idx
            .entry(poly_name.clone())
            .or_default()
            .push((mono_name.clone(), mono_ty));
    }

    pub fn mono_fn_externs(self) -> HashMap<Path, Vec<(Path, Ty)>> {
        let extern_set = self.extern_set;
        self.poly_mono_fn_idx
            .into_iter()
            .flat_map(|(poly_fn, mono_fns)| {
                if extern_set.contains(&poly_fn) {
                    Some((poly_fn, mono_fns))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn monomorphize(&mut self) -> Vec<lir::Func> {
        /*
         * Due to changes in the solver, non-function types can also be quantified and/or qualified types.
         * This means that during code generation, values can be polymorphic and must be monomorphized in
         * the same way that polymorphic functions are monomorphized. This _should_ be relatively
         * straightforward: modify the monomorphization process to search for values (not just functions)
         * that are polymorphic. These can be then treated as polymorphic "call sites" and thus be
         * branched accordingly.
         */

        log::debug!("[monomorphize] BEGIN");
        let mut globals = vec![];
        let mut funcs = vec![];
        let rc_prog = Rc::clone(&self.program);
        let mut prog = RefCell::borrow_mut(&rc_prog);

        // monomorphize polymorphic functions that are called from non-polymorphic functions
        for func in prog.funcs.iter_mut() {
            // NOTE: only calls within _monomorphic_ functions can be monomorphized
            if !func.ty.is_polymorphic() {
                self.monomorphize_func(func, &mut funcs, &mut globals);
            }
        }

        funcs
    }

    fn monomorphize_func(
        &mut self,
        func: &mut lir::Func,
        funcs: &mut Vec<lir::Func>,
        globals: &mut Vec<lir::Global>,
    ) {
        let mut symbols = func.symbols.clone();
        let mut poly_refs = vec![];
        let mut locals = HashMap::new();
        let func_name = func.name.clone();
        self.collect(func.into_iter(), &mut poly_refs);

        for mut poly_ref in poly_refs {
            log::debug!("[monomorphize] {:?}", poly_ref);
            if let Some((poly_name, mono_name)) =
                self.monomorphize_ref(&mut poly_ref, &mut locals, funcs, globals)
            {
                log::debug!("symbols for `{}`: {:?}", func_name, symbols);
                log::debug!("poly_name: {}", poly_name);
                log::debug!("mono_name: {}", mono_name);
                if poly_name == mono_name {
                    continue;
                }

                let base_poly_name = poly_name.without_func_type();

                // remove from the name set
                self.name_set.remove(&base_poly_name);
                self.name_set.insert(mono_name.clone());

                // remove from the function symbols
                symbols.remove(&poly_name);
                symbols.remove(&base_poly_name);
                symbols.insert(mono_name);
            }
        }

        // now for each local in the map, set the type of the local in the function
        for (loc, ty) in locals {
            func.set_ty_of_local(loc, ty);
        }

        func.symbols = symbols;
    }

    fn monomorphize_ref(
        &mut self,
        poly_ref: &mut PolyRef<'_>,
        locals: &mut HashMap<usize, TyScheme>,
        funcs: &mut Vec<lir::Func>,
        globals: &mut Vec<lir::Global>,
    ) -> Option<(Path, Path)> {
        match &mut poly_ref.value {
            PolyValue::Call(call) => Some(self.monomorphize_call(
                call,
                &poly_ref.poly_ty,
                &mut poly_ref.callee_ty,
                locals,
                funcs,
                globals,
            )),
            PolyValue::FuncRef(func_ref) => Some(self.monomorphize_func_ref(
                func_ref,
                &poly_ref.poly_ty,
                &mut poly_ref.callee_ty,
                funcs,
                globals,
            )),
        }
    }

    #[inline]
    fn is_trait_or_extern(&self, p: &Path) -> bool {
        let key = p.with_names_only();
        if self.extern_set.contains(&key) {
            return true;
        }

        if let Some(base) = key.name() {
            if self
                .extern_set
                .iter()
                .any(|q| q.name().map_or(false, |qb| qb == base))
            {
                log::debug!(
                    "[monomorphize] is_trait_or_extern base-name match: {} ~ {:?}",
                    base,
                    key
                );
                return true;
            }
        }
        return false;
    }

    /// Resolve a trait method call to its concrete impl function name.
    ///
    /// When a polymorphic function calls a trait method (e.g., `core::Neq::!=`),
    /// the concrete implementation is named by the impl path (e.g., `core::uint::!=`).
    /// This method bridges that naming gap by searching `impls_by_trait` for a
    /// matching impl field and checking if the mangled name exists in `name_set`.
    fn resolve_trait_method_name(
        &self,
        poly_fqn: &Path,
        callee_ty: &TyScheme,
    ) -> Option<Path> {
        let trait_path = ItemPath::from(&poly_fqn.parent());
        let method_name = poly_fqn.name()?;
        let impls = self.impls_by_trait.get(&trait_path)?;
        for impl_ty in impls {
            for field in &impl_ty.fields {
                if field.path.item_name() != Some(&method_name) {
                    continue;
                }
                let candidate = mangle::fn_name(&field.path.to_path(), callee_ty);
                if self.name_set.contains(&candidate) {
                    return Some(candidate);
                }
            }
        }
        None
    }

    fn monomorphize_call(
        &mut self,
        call: &mut lir::Call,
        poly_ty: &TyScheme,
        callee_ty: &mut TyScheme,
        locals: &mut HashMap<usize, TyScheme>,
        funcs: &mut Vec<lir::Func>,
        globals: &mut Vec<lir::Global>,
    ) -> (Path, Path) {
        // NOTE: unless there's a bug in the compiler, the callee function type is always monomorphic
        // Function types that make it here are either contained in a pure-monomorphic
        // function, which means that the call will have a concrete type, or
        // the type is contained in a monomorphized polymorphic function in which case
        // the function type has been monomorphized previously

        // with_names_only() also removes function type suffixes; no need to call without_func_type()
        let poly_fqn = call.orig_name().with_names_only();
        log::debug!("[monomorphize] poly_fqn: {}", poly_fqn);
        log::debug!("[monomorphize] poly_ty: {}", poly_ty);
        log::debug!("[monomorphize] callee_ty: {}", callee_ty);
        // Free-var fingerprints using real type vars (no string scanning)
        let fv_poly: Vec<_> = poly_ty.free_vars().into_iter().cloned().collect();
        let fv_callee: Vec<_> = callee_ty.free_vars().into_iter().cloned().collect();
        log::debug!("[monomorphize] fv(poly_ty)   = {:?}", fv_poly);
        log::debug!("[monomorphize] fv(callee_ty) = {:?}", fv_callee);

        log::debug!("[monomorphize] call.orig_name = {}", call.orig_name());
        log::debug!("[monomorphize] call.name      = {}", call.fn_name);
        log::debug!("[monomorphize] call.ty        = {}", call.callee_ty);
        log::debug!("[monomorphize] call.args      = {:?}", call.args);

        let fn_name = call.fn_name.clone();
        let original_name = call.orig_name().clone();
        let (poly_name, mono_name, mono_ty, update_locals) = self.resolve_callee(
            &poly_fqn,
            &fn_name,
            &original_name,
            poly_ty,
            callee_ty,
            funcs,
            globals,
        );

        call.set_name(mono_name.clone());
        call.callee_ty = mono_ty.clone();

        if update_locals {
            for (idx, arg) in call.args.iter().enumerate() {
                if let &lir::Variable::Local(loc) = arg {
                    if let Some(ty) = mono_ty.mono().get_func_param(idx).cloned() {
                        log::debug!("adding local with type {}: {}", loc, ty);
                        // FIXME: what if the loc is already in the map with another type?
                        locals.insert(loc, ty.into());
                    }
                }
            }
        }

        (poly_name, mono_name)
    }

    fn resolve_callee(
        &mut self,
        poly_fqn: &Path,
        current_name: &Path,
        original_name: &Path,
        poly_ty: &TyScheme,
        callee_ty: &TyScheme,
        funcs: &mut Vec<lir::Func>,
        globals: &mut Vec<lir::Global>,
    ) -> (Path, Path, TyScheme, bool) {
        let poly_fqn = poly_fqn.with_names_only();

        // Fast path: externs are not monomorphized here.
        // We already have the concrete resolved name in the call; just return it.
        let is_extern_like = self.is_trait_or_extern(&poly_fqn)
            || self.is_trait_or_extern(current_name)
            || self.is_trait_or_extern(original_name);
        if is_extern_like {
            // Keep the polymorphic side as the logical (names-only) key, but use the concrete name for mono.
            let poly_name = mangle::fn_name(&poly_fqn.with_names_only(), poly_ty);
            let mono_name = current_name.clone();
            log::debug!(
                "[monomorphize] fast-path extern: poly_name={} mono_name={}",
                poly_name,
                mono_name
            );
            self.mono_poly_fn_idx
                .insert(poly_name.clone(), mono_name.clone());
            self.add_mono_fn_mapping(&poly_name, &mono_name, callee_ty.clone().into_mono());
            return (poly_name, mono_name, callee_ty.clone(), false);
        }

        // Fast path: trait member calls where the concrete impl already exists.
        // Polymorphic functions reference trait methods (e.g., `core::Neq::!=`) but
        // the actual functions are named by their impl path (e.g., `core::uint::!=`).
        // Resolve the trait method name to the concrete impl name via impls_by_trait.
        let trait_key = poly_fqn.with_names_only();
        if self.trait_member_set.contains(&trait_key) {
            if let Some(resolved_mono) = self.resolve_trait_method_name(&poly_fqn, callee_ty) {
                let poly_name = mangle::fn_name(&poly_fqn.with_names_only(), poly_ty);
                log::debug!(
                    "[monomorphize] fast-path trait member: poly_name={} mono_name={}",
                    poly_name,
                    resolved_mono
                );
                self.mono_poly_fn_idx
                    .insert(poly_name.clone(), resolved_mono.clone());
                self.add_mono_fn_mapping(
                    &poly_name,
                    &resolved_mono,
                    callee_ty.clone().into_mono(),
                );
                return (poly_name, resolved_mono, callee_ty.clone(), false);
            }
        }

        // check that the callee function type is monomorphic
        if callee_ty.is_polymorphic() {
            log::debug!(
                "[monomorphize] callee type is not monomorphic: {}",
                callee_ty
            );
            log::debug!("[monomorphize]   here's the polymorphic type: {}", poly_ty);

            // Diagnostic: try an MGU on the monomorphic shapes to see if the shape would bind vars here.
            match mgu(poly_ty.mono(), callee_ty.mono()) {
                Ok((_, test_subst)) => {
                    log::debug!(
                        "[monomorphize] (diag) mgu(poly.mono, callee.mono) = {:#?}",
                        test_subst
                    );
                    let fv_callee_now: Vec<_> =
                        callee_ty.free_vars().into_iter().cloned().collect();
                    for tv in &fv_callee_now {
                        let present = test_subst.contains_key(tv);
                        log::debug!(
                            "[monomorphize] (diag) var {:?} present_in_mgu_subst = {}",
                            tv,
                            present
                        );
                    }
                }
                Err(_) => {
                    log::debug!("[monomorphize] (diag) mgu(poly.mono, callee.mono) = <none>");
                }
            }

            panic!(
                "cannot monomorphize function where the callee type is polymorphic: {}",
                callee_ty
            );
        }

        // get the polymorphic name (logical key) and resolve the concrete impl by types
        let poly_base_name = poly_fqn.clone();
        let poly_name = mangle::fn_name(&poly_base_name, poly_ty);

        // Pick a concrete polymorphic implementation matching the callee type.
        // Collect candidate keys: start with poly_fqn, and if it's a trait member,
        // also try the impl field paths from impls_by_trait.
        let mut subst = Subst::new();
        let mut selected_fn: Option<lir::Func> = None;

        let mut candidate_keys = vec![poly_fqn.clone()];
        let trait_key = poly_fqn.with_names_only();
        if self.trait_member_set.contains(&trait_key) {
            if let Some(method_name) = poly_fqn.name() {
                let trait_path = ItemPath::from(&poly_fqn.parent());
                if let Some(impls) = self.impls_by_trait.get(&trait_path) {
                    for impl_ty in impls {
                        for field in &impl_ty.fields {
                            if field.path.item_name() == Some(&method_name) {
                                let impl_method_path = field.path.to_path();
                                if impl_method_path != poly_fqn {
                                    candidate_keys.push(impl_method_path);
                                }
                            }
                        }
                    }
                }
            }
        }

        for cand_key in &candidate_keys {
            let Some(cand_fns) = self.poly_fn_map.get(cand_key) else {
                continue;
            };
            for cand_fn in cand_fns {
                let Some(s) = match_scheme_vars(&cand_fn.ty, callee_ty) else {
                    continue;
                };

                if let Some(unsatisfied_predicates) =
                    self.candidate_is_applicable(&cand_fn.ty, &s)
                {
                    log::debug!(
                        "[monomorphize] rejected impl {} for {} due to unsatisfied qualifiers: [{}]",
                        cand_key,
                        poly_fqn,
                        join(&unsatisfied_predicates, ", ")
                    );
                    continue;
                }

                log::debug!("[monomorphize] selected impl {} for {}", cand_fn.name, poly_fqn);
                subst = s;
                selected_fn = Some(cand_fn.clone());
                break;
            }
            if selected_fn.is_some() {
                break;
            }
        }

        if selected_fn.is_none() {
            let s = match_scheme_vars(poly_ty, callee_ty).unwrap_or_default();
            log::debug!(
                "[monomorphize] fallback for {} using subst = {:#?}",
                poly_fqn,
                s
            );
            subst = s;
        }

        // get the monomorphized name using the callee type
        log::debug!("[monomorphize] subst = {:#?}", subst);
        let mono_base_name = poly_fqn.clone();
        let mono_name = mangle::fn_name(&mono_base_name, callee_ty);
        let mono_ty = callee_ty.clone();

        log::debug!("[monomorphize] poly_name = {}", poly_name);
        log::debug!("[monomorphize] mono_name = {}", mono_name);

        let (resolved_poly_name, resolved_mono_name) = if self.name_set.contains(&mono_name) {
            (poly_base_name, mono_name.clone())
        } else {
            let mut mono_fn = match selected_fn {
                Some(f) => f,
                None => {
                    panic!(
                        "polymorphic function `{}` is undefined. here are the defined functions:\n{}",
                        poly_fqn,
                        self.poly_fn_map
                            .keys()
                            .map(|a| format!("  {}", a))
                            .join("\n")
                    )
                }
            };
            mono_fn.name = mono_name.clone();
            mono_fn.ty = mono_ty.clone();

            log::debug!(
                "[monomorphize] before apply_subst: mono_name={} mono_ty={} symbols={:?}",
                mono_name,
                mono_ty,
                mono_fn.symbols
            );

            // BEFORE substitution
            let tvs_before = scan_tyvars_in_paths(&mono_fn.symbols);
            log::debug!(
                "[monomorphize] tvs in symbols before subst for `{}`: {:?}",
                mono_name,
                tvs_before
            );
            log::debug!(
                "[monomorphize] subst bindings for `{}`: {:?}",
                mono_name,
                subst
            );

            // apply the substitution to the function
            mono_fn.apply_subst(&subst);
            log::debug!(
                "[monomorphize] symbols for `{}` after subst: {:?}",
                mono_name,
                mono_fn.symbols
            );

            // summary
            let tvs_after = scan_tyvars_in_paths(&mono_fn.symbols);
            log::debug!(
                "[monomorphize] tvs in symbols after subst for `{}`: {:?}",
                mono_name,
                tvs_after
            );

            // per symbol details
            for p in mono_fn.symbols.iter() {
                let s = p.to_string();
                if s.contains("?t") || s.contains("?s") || s.contains("?k") {
                    log::warn!(
                        "[monomorphize] unresolved tyvar in `{}` of `{}`",
                        s,
                        mono_name
                    );
                }
            }

            self.monomorphize_func(&mut mono_fn, funcs, globals);
            log::debug!(
                "[monomorphize] params for `{}`: {:?}",
                mono_name,
                mono_fn.params
            );
            log::debug!(
                "[monomorphize] locals for `{}`: {:?}",
                mono_name,
                mono_fn.locals
            );
            funcs.push(mono_fn);
            (poly_name, mono_name.clone())
        };

        self.mono_poly_fn_idx
            .insert(resolved_poly_name.clone(), resolved_mono_name.clone());
        self.add_mono_fn_mapping(
            &resolved_poly_name,
            &resolved_mono_name,
            mono_ty.clone().into_mono(),
        );
        (resolved_poly_name, resolved_mono_name, mono_ty, true)
    }

    fn monomorphize_func_ref(
        &mut self,
        func_ref: &mut lir::FuncRef,
        poly_ty: &TyScheme,
        callee_ty: &mut TyScheme,
        funcs: &mut Vec<lir::Func>,
        globals: &mut Vec<lir::Global>,
    ) -> (Path, Path) {
        let poly_fqn = func_ref.original_path.with_names_only();
        let current_name = func_ref.path.clone();
        let original_name = func_ref.original_path.clone();
        let (poly_name, mono_name, mono_ty, _) = self.resolve_callee(
            &poly_fqn,
            &current_name,
            &original_name,
            poly_ty,
            callee_ty,
            funcs,
            globals,
        );
        func_ref.path = mono_name.clone();
        func_ref.ty = mono_ty;
        (poly_name, mono_name)
    }

    fn collect<'a, T>(&self, insts: T, poly_refs: &mut Vec<PolyRef<'a>>)
    where
        T: Iterator<Item = &'a mut lir::Inst>,
    {
        for inst in insts {
            match inst {
                lir::Inst::SetGlobal(_, v)
                | lir::Inst::SetLocal(_, v)
                | lir::Inst::IncRef(v, _)
                | lir::Inst::DecRef(v)
                | lir::Inst::Return(v) => self.add_ref_from_value(v, poly_refs),
                lir::Inst::Store(s) => self.add_ref_from_value(&mut s.value, poly_refs),
                lir::Inst::Insert(i) => self.add_ref_from_value(&mut i.value, poly_refs),
                lir::Inst::SetField(s) => self.add_ref_from_value(&mut s.value, poly_refs),
                lir::Inst::Call(call) => self.add_call_ref(poly_refs, call),

                lir::Inst::Free(_)
                | lir::Inst::CExternCall(_)
                | lir::Inst::StructInit(_, _)
                | lir::Inst::MemCopy(_, _, _)
                | lir::Inst::If(_)
                | lir::Inst::Break(_)
                | lir::Inst::Goto(_) => continue,
            }
        }
    }

    fn add_ref_from_value<'a>(&self, value: &'a mut lir::Value, poly_refs: &mut Vec<PolyRef<'a>>) {
        match value {
            lir::Value::Atom(a) => match a {
                lir::Atom::FuncRef(func_ref) => {
                    let callee_ty = func_ref.ty.clone();
                    let poly_ty = unless!(&func_ref.poly_ty).clone();

                    poly_refs.push(PolyRef {
                        value: PolyValue::FuncRef(func_ref),
                        poly_ty,
                        callee_ty,
                    });
                }
                _ => {}
            },
            lir::Value::Call(call) => self.add_call_ref(poly_refs, call),
            lir::Value::CExternCall(_) => todo!(),
            _ => {}
        };
    }

    fn add_call_ref<'a>(&self, poly_refs: &mut Vec<PolyRef<'a>>, call: &'a mut lir::Call) {
        log::debug!("[monomorphize] add_call_ref: {}", call);
        if call.fn_ref.is_some() {
            log::debug!("[monomorphize] skipping for fn_ref in call: {}", call);
            return;
        }
        let callee_ty = call.callee_ty.clone();
        let Some(poly_ty) = call.poly_callee_ty.clone() else {
            log::debug!(
                "[monomorphize] skipping for call (not a polymorphic function): {}",
                call
            );
            return;
        };
        poly_refs.push(PolyRef {
            value: PolyValue::Call(call),
            poly_ty,
            callee_ty,
        });
    }
}

// fn apply_trait_defaults(ty: &mut TyScheme) -> Option<Subst<TyVar, Ty>> {
//     if ty.qualifiers().is_empty() {
//         return None;
//     }

//     let subst = ty
//         .qualifiers()
//         .iter()
//         .flat_map(|p| {
//             p.type_params().and_then(|ty_params| {
//                 if p.is_int_trait() {
//                     Some((variant!(&ty_params[0], if Ty::Var(a)).clone(), Ty::int()))
//                 } else if p.is_float_trait() {
//                     Some((variant!(&ty_params[0], if Ty::Var(a)).clone(), Ty::float()))
//                 } else {
//                     None
//                 }
//             })
//         })
//         .collect::<Subst<TyVar, Ty>>();
//     ty.apply_subst(&subst);
//     Some(subst)
// }

fn scan_tyvars_in_paths(paths: &std::collections::HashSet<Path>) -> Vec<String> {
    fn scan_substring(s: &str, sub: &str, out: &mut Vec<String>) {
        // very simple scan for substrings
        let mut i = 0;
        while let Some(pos) = s[i..].find(sub) {
            let start = i + pos;
            let mut end = start + 2;
            while end < s.len() && s.as_bytes()[end].is_ascii_digit() {
                end += 1;
            }
            out.push(s[start..end].to_string());
            i = end;
        }
    }

    let mut out = Vec::new();
    for p in paths {
        let s = p.to_string();
        // very simple scan for substrings like ?t123
        scan_substring(&s, "?t", &mut out);
        scan_substring(&s, "?tm", &mut out);
        scan_substring(&s, "?s", &mut out);
        scan_substring(&s, "?k", &mut out);
    }
    out.sort();
    out.dedup();
    out
}
