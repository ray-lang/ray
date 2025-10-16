use std::collections::{HashMap, HashSet};

use top::{
    Class, Instance, Predicate, Predicates, Substitutable,
    solver::{SolveOptions, SolveResult, Solver, greedy::GreedySolver},
};

use crate::{
    sema::NameContext,
    span::SourceMap,
    typing::{bound_names::BoundNames, state::Env, traits::QualifyTypes},
};

use super::{
    TypeError,
    collect::{CollectConstraints, CollectCtx},
    constraints::tree::BottomUpWalk,
    context::TyCtx,
    info::TypeSystemInfo,
    state::SchemeEnv,
    ty::{Ty, TyVar},
};

pub(crate) mod solution;

#[derive(Debug)]
pub struct InferSystem<'a> {
    tcx: &'a mut TyCtx,
    ncx: &'a mut NameContext,
}

impl<'a> InferSystem<'a> {
    pub fn new(tcx: &'a mut TyCtx, ncx: &'a mut NameContext) -> InferSystem<'a> {
        InferSystem { tcx, ncx }
    }

    pub fn infer_ty<T, U>(
        &mut self,
        v: &T,
        srcmap: &mut SourceMap,
        defs: SchemeEnv,
    ) -> Result<(SolveResult<TypeSystemInfo, Ty, TyVar>, SchemeEnv), Vec<TypeError>>
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
            defs,
        };
        let (_, _, c) = v.collect_constraints(&mut ctx);
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        log::debug!("{}", v);
        // log::debug!("constraints: {:#?}", constraints);
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
            let superclasses = trait_ty
                .super_traits
                .iter()
                .map(|super_trait| super_trait.get_path().unwrap().to_string())
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
                            Instance::new(
                                Predicate::class(
                                    impl_ty.trait_ty.get_path().unwrap().to_string(),
                                    base_ty,
                                ),
                                Predicates::from(impl_ty.predicates.clone()),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default();
            let class = Class::new(superclasses, instances);
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

        // let (mut solution, constraints) = solver.solve(options, constraints);
        let mut solution = solver.solve(options, constraints);
        // normalize the skolems
        solution.normalize_subst();

        log::debug!("solution: {}", solution);

        if solution.errors.len() != 0 {
            let errs = solution
                .errors
                .into_iter()
                .map(|(_, info)| TypeError::from_info(info))
                .collect();
            Err(errs)
        } else {
            log::debug!("defs: {:?}", defs);
            defs.apply_subst_all(&solution.subst);
            defs.qualify_tys(&solution.qualifiers);
            log::debug!("defs: {}", defs);
            Ok((solution, defs))
        }
    }
}
