use ray_shared::collections::namecontext::NameContext;
use ray_typing::{ModuleInput, TypeCheckResult, TypecheckOptions, check_module, tyctx::TyCtx};

use crate::{
    ast::{Decl, Module},
    passes::{
        binding::{self, BindingPassOutput},
        call_resolution,
        closure::{self, ClosurePassOutput},
        extern_bindings,
    },
    sourcemap::SourceMap,
    typing::lower_module,
};

/// Simple orchestration helper for frontend passes. It runs binding analysis,
/// closure capture, and exposes their outputs to downstream consumers.
pub struct FrontendPassManager<'a> {
    module: &'a Module<(), Decl>,
    srcmap: &'a SourceMap,
    tcx: &'a mut TyCtx,
    binding_output: Option<BindingPassOutput>,
    closure_output: Option<ClosurePassOutput>,
    lowered_input: Option<ModuleInput>,
    typecheck_result: Option<TypeCheckResult>,
}

impl<'a> FrontendPassManager<'a> {
    pub fn new(module: &'a Module<(), Decl>, srcmap: &'a SourceMap, tcx: &'a mut TyCtx) -> Self {
        Self {
            module,
            srcmap,
            tcx,
            binding_output: None,
            closure_output: None,
            lowered_input: None,
            typecheck_result: None,
        }
    }

    fn ensure_binding_output(&mut self) {
        if self.binding_output.is_none() {
            let mut seed = BindingPassOutput::empty();
            extern_bindings::inject_extern_bindings(&mut seed, self.tcx.schemes());
            let output =
                binding::run_binding_pass(self.module, self.srcmap, &self.tcx.global_env, seed);
            self.binding_output = Some(output);
        }
    }

    /// Ensure the binding pass has been executed and return its results.
    pub fn binding_output(&mut self) -> &BindingPassOutput {
        self.ensure_binding_output();
        self.binding_output
            .as_ref()
            .expect("binding pass output should exist")
    }

    fn ensure_closure_output(&mut self) {
        if self.closure_output.is_none() {
            self.ensure_binding_output();
            let binding_output = self
                .binding_output
                .as_ref()
                .expect("binding pass output should exist");
            let output = closure::run_closure_pass(self.module, self.srcmap, binding_output);
            self.closure_output = Some(output);
        }
    }

    pub fn closure_output(&mut self) -> &ClosurePassOutput {
        self.ensure_closure_output();
        self.closure_output
            .as_ref()
            .expect("closure pass output should exist")
    }

    fn ensure_typecheck(&mut self, ncx: &NameContext, options: TypecheckOptions) {
        if self.typecheck_result.is_none() {
            self.ensure_closure_output();
            let binding_output = self
                .binding_output
                .as_ref()
                .expect("binding pass output should exist");
            let schema_allocator = self.tcx.schema_allocator();
            let input = lower_module(
                self.module,
                self.srcmap,
                &self.tcx.global_env,
                binding_output,
                schema_allocator,
            );
            self.lowered_input = Some(input);
            let input = self
                .lowered_input
                .as_ref()
                .expect("lowered module input should exist");

            let mut result = check_module(input, options, self.tcx, ncx);
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
        (
            self.binding_output
                .expect("binding pass output should exist"),
            self.closure_output
                .expect("closure pass output should exist"),
            self.typecheck_result
                .expect("typecheck result should exist"),
        )
    }
}
