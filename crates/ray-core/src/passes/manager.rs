use std::collections::HashMap;

use ray_shared::{collections::namecontext::NameContext, node_id::NodeId, resolution::Resolution};
use ray_typing::{
    TypeCheckInput, TypeCheckResult, TypecheckOptions, mocks::MockTypecheckEnv, tyctx::TyCtx,
    typecheck,
};

use crate::{
    ast::{Decl, Module},
    passes::{
        binding::{self, BindingPassOutput},
        call_resolution,
        closure::{self, ClosurePassOutput},
        deps::build_binding_graph,
        extern_bindings,
    },
    sourcemap::SourceMap,
    typing::{build_typecheck_input, collect_def_ids},
};

/// Simple orchestration helper for frontend passes. It runs binding analysis,
/// closure capture, and exposes their outputs to downstream consumers.
pub struct FrontendPassManager<'a> {
    module: &'a Module<(), Decl>,
    srcmap: &'a SourceMap,
    tcx: &'a mut TyCtx,
    resolutions: &'a HashMap<NodeId, Resolution>,
    lowered_input: Option<TypeCheckInput>,
    typecheck_result: Option<TypeCheckResult>,
}

impl<'a> FrontendPassManager<'a> {
    pub fn new(
        module: &'a Module<(), Decl>,
        srcmap: &'a SourceMap,
        tcx: &'a mut TyCtx,
        resolutions: &'a HashMap<NodeId, Resolution>,
    ) -> Self {
        Self {
            module,
            srcmap,
            tcx,
            resolutions,
            lowered_input: None,
            typecheck_result: None,
        }
    }

    fn ensure_binding_output(&mut self) {
        unreachable!()
    }

    /// Ensure the binding pass has been executed and return its results.
    pub fn binding_output(&mut self) -> &BindingPassOutput {
        unreachable!()
    }

    fn ensure_closure_output(&mut self) {
        unreachable!()
    }

    pub fn closure_output(&mut self) -> &ClosurePassOutput {
        unreachable!()
    }

    fn ensure_typecheck(&mut self, ncx: &NameContext, options: TypecheckOptions) {
        if self.typecheck_result.is_none() {
            self.ensure_closure_output();

            // Build DefId-keyed structures for the new typechecker.
            let all_defs = collect_def_ids(self.module);
            let def_bindings = build_binding_graph(&all_defs, self.resolutions);

            let typecheck_env = MockTypecheckEnv::new();
            let input = build_typecheck_input(
                &self.module.decls,
                &[],
                self.srcmap,
                &typecheck_env,
                self.resolutions,
                def_bindings,
            );
            self.lowered_input = Some(input);
            let input = self
                .lowered_input
                .as_ref()
                .expect("lowered module input should exist");

            let mut result = typecheck(input, options, self.tcx, &typecheck_env);
            if !input.lowering_errors.is_empty() {
                let mut errors = input.lowering_errors.clone();
                errors.extend(result.errors);
                result.errors = errors;
            }

            call_resolution::run_call_resolution_pass(input, self.tcx, ncx);
            self.typecheck_result = Some(result);
        }
    }

    pub fn typecheck(&mut self, ncx: &NameContext, options: TypecheckOptions) -> &TypeCheckResult {
        self.ensure_typecheck(ncx, options);
        self.typecheck_result
            .as_ref()
            .expect("typecheck result should exist")
    }

    /// Run all frontend passes (binding + closure + typecheck) and return their outputs.
    pub fn run_passes(
        mut self,
        ncx: &NameContext,
        options: TypecheckOptions,
    ) -> (BindingPassOutput, ClosurePassOutput, TypeCheckResult) {
        self.ensure_binding_output();
        self.ensure_closure_output();
        self.ensure_typecheck(ncx, options);
        unreachable!()
    }
}
