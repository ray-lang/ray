use std::collections::HashSet;

use top::{
    Class, Instance, Predicate, Predicates, Subst, Substitutable, mgu, mgu_with_synonyms,
    solver::{SolveOptions, SolveResult, Solver, greedy::GreedySolver},
};

use crate::{
    errors::RayError,
    sema::NameContext,
    span::SourceMap,
    typing::{
        TypeErrorKind, bound_names::BoundNames, constraints::tree::BottomUpWalk, state::Env,
        traits::QualifyTypes,
    },
};

use super::{
    TypeError,
    collect::{CollectConstraints, CollectCtx},
    context::TyCtx,
    info::TypeSystemInfo,
    state::SchemeEnv,
    ty::{Ty, TyVar},
};

#[derive(Debug)]
pub struct InferSystem<'a> {
    tcx: &'a mut TyCtx,
    ncx: &'a mut NameContext,
}

pub struct InferResult {
    pub solution: SolveResult<TypeSystemInfo, Ty, TyVar>,
    pub defs: SchemeEnv,
    pub errors: Vec<TypeError>,
}

impl<'a> InferSystem<'a> {
    pub fn new(tcx: &'a mut TyCtx, ncx: &'a mut NameContext) -> InferSystem<'a> {
        InferSystem { tcx, ncx }
    }

    pub fn infer<T, U>(
        tcx: &'a mut TyCtx,
        ncx: &'a mut NameContext,
        srcmap: &SourceMap,
        v: &T,
        defs: &SchemeEnv,
    ) -> InferResult
    where
        T: CollectConstraints<Output = U> + std::fmt::Display,
    {
        let mut infer_system = InferSystem::new(tcx, ncx);
        infer_system.infer_ty(v, srcmap, defs)
    }

    pub fn infer_ty<T, U>(&mut self, v: &T, srcmap: &SourceMap, defs: &SchemeEnv) -> InferResult
    where
        T: CollectConstraints<Output = U> + std::fmt::Display,
    {
        let mono_tys = HashSet::new();
        let mut new_defs = Env::new();
        let mut ctx = CollectCtx {
            mono_tys: &mono_tys,
            srcmap: &srcmap,
            tcx: self.tcx,
            ncx: self.ncx,
            new_defs: &mut new_defs,
            bound_names: &mut BoundNames::new(),
            defs: defs.clone(),
        };
        let (_, _, c) = v.collect_constraints(&mut ctx);
        log::debug!("constraint tree: {:?}", c);

        let constraints = c.clone().spread().phase().flatten_bottom_up();
        log::debug!("{}", v);
        let mut s = String::new();
        s.push_str("[\n");
        for constraint in constraints.iter() {
            s.push_str(&format!("  {}\n", constraint));
        }
        s.push_str("]");

        log::debug!("constraints: {}", s);

        // combine with the new definitions collected from constraints
        let mut defs = ctx.defs;
        defs.extend(new_defs);

        let solver = GreedySolver::default(); //new(constraints, &mut self.tcx);
        let mut options = SolveOptions::default();
        options.unique = self.tcx.tf().curr() as u32;

        // convert the traits/impls into classes/instances
        for (path, trait_ty) in self.tcx.traits() {
            let param_vars = trait_ty
                .ty
                .get_ty_params()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            let superclasses = trait_ty
                .super_traits
                .iter()
                .map(|super_trait| {
                    (
                        super_trait.get_path().to_string(),
                        super_trait
                            .get_ty_params()
                            .into_iter()
                            .cloned()
                            .collect::<Vec<_>>(),
                    )
                })
                .collect();
            let instances = self
                .tcx
                .impls()
                .get(path)
                .map(|impls| {
                    impls
                        .iter()
                        .map(|impl_ty| {
                            let base_ty = impl_ty.base_ty.clone();
                            let ty_args = impl_ty.ty_args.clone();
                            Instance::new(
                                Predicate::class(
                                    impl_ty.trait_ty.get_path().without_type_args().to_string(),
                                    base_ty,
                                    ty_args,
                                ),
                                Predicates::from(impl_ty.predicates.clone()),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default();
            let class = Class::new(param_vars, superclasses, instances);
            options.class_env.add_class(path.to_string(), class);
            options
                .type_class_directives
                .extend(trait_ty.directives.clone());
        }

        // convert structs to record classes
        for (_, struct_ty) in self.tcx.structs() {
            for (field_name, field_ty) in struct_ty.fields.iter() {
                options.class_env.add_record_class(
                    field_name.clone(),
                    Predicate::has_field(
                        struct_ty.ty.mono().clone(),
                        field_name.clone(),
                        field_ty.mono().clone(),
                    ),
                )
            }
        }

        log::debug!("class env: {:?}", options.class_env);

        let mut solution = solver.solve(options, constraints);
        // normalize the skolems
        solution.normalize_subst();

        log::debug!("solution: {}", solution);

        log::debug!("defs: {:?}", defs);

        for skolem in solution.skolems.iter() {
            for (u, v) in skolem.vars.iter() {
                // skolem vars map: v -> u, so look to see if we have
                // v in the inverted var map, and if we do, also add u
                let mapped_var = {
                    let map = self.tcx.inverted_var_map().borrow();
                    match map.get(v).cloned() {
                        Some(m) => m,
                        _ => continue,
                    }
                };

                log::debug!(
                    "found {} -> {}, adding {} -> {}",
                    v,
                    mapped_var,
                    u,
                    mapped_var
                );
                self.tcx
                    .inverted_var_map()
                    .borrow_mut()
                    .insert(u.clone(), mapped_var);
            }
        }

        log::debug!(
            "inverted var map: {:?}",
            self.tcx.inverted_var_map().borrow()
        );

        // Always apply the solution's substitution and qualifiers to defs so
        // callers (e.g., IDE/LSP) can see as much inferred type information as
        // possible, even when there are type errors.
        defs.apply_subst_all(&solution.subst);
        defs.qualify_tys(&solution.qualifiers);

        // Build a list of TypeError values from solver errors and
        // post-inference checks, but do not abort; callers can decide whether
        // to treat these as fatal.
        let mut errors: Vec<TypeError> = Vec::new();
        if !solution.errors.is_empty() {
            let mut rename_subst = self
                .tcx
                .inverted_var_map()
                .borrow()
                .iter()
                .map(|(u, v)| (u.clone(), Ty::Var(v.clone())))
                .collect::<Subst<_, _>>();

            let skolem_subst = solution
                .skolems
                .iter()
                .flat_map(|skolem| {
                    skolem.vars.iter().map(|(skolem_var, original)| {
                        (skolem_var.clone(), Ty::Var(original.clone()))
                    })
                })
                .collect::<Subst<_, _>>();

            rename_subst.union(skolem_subst);

            log::debug!("[infer_ty] rename_subst = {:?}", rename_subst);

            errors.extend(solution.errors.drain(..).map(|(label, mut info)| {
                info.apply_subst(&solution.subst);
                info.apply_subst(&rename_subst);
                info.simplify();
                TypeError::from_info(label, info)
            }));
        }

        if let Err(mut post_errs) = self.post_infer_checks(&defs, &solution, &srcmap) {
            errors.append(&mut post_errs);
        }

        log::debug!("defs: {}", defs);
        InferResult {
            solution,
            defs,
            errors,
        }
    }

    fn post_infer_checks(
        &self,
        defs: &SchemeEnv,
        solution: &SolveResult<TypeSystemInfo, Ty, TyVar>,
        _srcmap: &SourceMap,
    ) -> Result<(), Vec<TypeError>> {
        let mut errors: Vec<TypeError> = Vec::new();
        debug_assert!(solution.errors.is_empty());
        let var_subst: Subst<_, _> = self
            .tcx
            .inverted_var_map()
            .borrow()
            .iter()
            .map(|(u, v)| (u.clone(), Ty::Var(v.clone())))
            .collect();
        for (trait_path, trait_ty) in self.tcx.traits() {
            if let Some(impls) = self.tcx.impls().get(trait_path) {
                for impl_ty in impls {
                    for field in impl_ty.fields.iter() {
                        // Build trait method path string
                        let trait_method_path = trait_ty
                            .create_method_path(&field.path.to_short_name(), None)
                            .with_names_only();
                        let Some(trait_scheme) = defs.get(&trait_method_path) else {
                            continue;
                        };

                        let Some(impl_scheme) = &field.scheme else {
                            continue;
                        };

                        let mut orig_trait_scheme = trait_scheme.clone();
                        orig_trait_scheme.apply_subst(&var_subst);

                        let mut args = Vec::new();
                        args.push(impl_ty.base_ty.clone());
                        args.extend(impl_ty.ty_args.clone());
                        let user_trait_scheme = orig_trait_scheme.instantiate_with_types(&args);

                        let mut user_impl_scheme = impl_scheme.clone();
                        user_impl_scheme.apply_subst(&var_subst);

                        match mgu(&user_trait_scheme.ty, user_impl_scheme.mono()) {
                            Ok((_, subst)) => {
                                // successful unification
                                log::debug!(
                                    "[post_infer_checks] unified {} and {}: subst={}",
                                    &user_trait_scheme.ty,
                                    user_impl_scheme.mono(),
                                    subst
                                );
                            }
                            Err(err) => {
                                log::debug!(
                                    "[post_infer_checks] failed to unify {} and {}: error={}",
                                    &user_trait_scheme.ty,
                                    user_impl_scheme.mono(),
                                    err
                                );
                                errors.push(TypeError {
                                    kind: TypeErrorKind::MismatchImpl(
                                        field.kind.to_string(),
                                        field.path.to_short_name(),
                                        user_trait_scheme.ty().clone(),
                                        user_impl_scheme.mono().clone(),
                                    ),
                                    src: vec![field.src.clone()],
                                })
                            }
                        }
                    }
                }
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}
