use inkwell::{
    builder::BuilderError,
    types::BasicMetadataTypeEnum,
    values::{
        BasicMetadataValueEnum, BasicValue as _, BasicValueEnum, CallSiteValue, FunctionValue,
        PointerValue,
    },
};
use ray_core::sourcemap::SourceMap;
use ray_lir::{self as lir};
use ray_shared::ty::Ty;

use crate::codegen::{Codegen as _, llvm::context::LLVMCodegenCtx};

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    pub(crate) fn build_call_args(
        &mut self,
        args: &Vec<lir::Variable>,
        expected_params: &Vec<BasicMetadataTypeEnum<'ctx>>,
        ray_param_tys: &Vec<Ty>,
        srcmap: &SourceMap,
    ) -> Result<Vec<BasicMetadataValueEnum<'ctx>>, BuilderError> {
        assert_eq!(
            expected_params.len(),
            ray_param_tys.len(),
            "callee LLVM param count and Ray param count must match for non-sret calls"
        );

        let arg_vals = args.codegen(self, srcmap);
        expected_params
            .iter()
            .zip(ray_param_tys.iter())
            .zip(arg_vals.into_iter())
            .map(|((expected, ray_param_ty), result)| {
                let v = result?;
                let marshalled = self.marshal_arg_value(ray_param_ty, expected, v)?;
                Ok(marshalled.into())
            })
            .collect()
    }

    /// Build a function call
    pub(crate) fn build_call(
        &mut self,
        function: FunctionValue<'ctx>,
        args: &Vec<lir::Variable>,
        expected_params: &Vec<BasicMetadataTypeEnum<'ctx>>,
        ray_param_tys: &Vec<Ty>,
        srcmap: &SourceMap,
    ) -> Result<CallSiteValue<'ctx>, BuilderError> {
        let args = self.build_call_args(args, expected_params, ray_param_tys, srcmap)?;
        self.builder.build_call(function, args.as_slice(), "")
    }

    pub(crate) fn build_sret_call_args(
        &mut self,
        args: &Vec<lir::Variable>,
        expected_params: &Vec<BasicMetadataTypeEnum<'ctx>>,
        ray_param_tys: &Vec<Ty>,
        ret_ty: &Ty,
        srcmap: &SourceMap,
    ) -> Result<(Vec<BasicMetadataValueEnum<'ctx>>, PointerValue<'ctx>), BuilderError> {
        let arg_vals = args.codegen(self, srcmap);

        // sret: allocate a local return slot, pass as first arg, and return the pointer as the value.
        let ret_slot = self.alloca(ret_ty)?;

        // prepend retptr then the rest of marshalled args
        let mut marshalled: Vec<BasicValueEnum> = Vec::with_capacity(expected_params.len());

        // First expected param must be a pointer (retptr)
        marshalled.push(ret_slot.as_basic_value_enum());

        assert_eq!(
            expected_params.len(),
            ray_param_tys.len() + 1,
            "sret calls expect one extra LLVM parameter (retptr) compared to Ray params"
        );

        // Zip remaining expected params with Ray param types and arg values.
        for ((expected, ray_param_ty), result) in expected_params
            .iter()
            .skip(1)
            .zip(ray_param_tys.iter())
            .zip(arg_vals.into_iter())
        {
            let v = result?;
            let arg = self.marshal_arg_value(ray_param_ty, expected, v)?;
            marshalled.push(arg);
        }

        // Collect all marshalled arguments (retptr + params) as metadata values.
        let marshalled_vals = marshalled.iter().map(|v| (*v).into()).collect::<Vec<_>>();
        Ok((marshalled_vals, ret_slot))
    }

    /// Build a function call with aggregate return type
    pub(crate) fn build_sret_call(
        &mut self,
        function: FunctionValue<'ctx>,
        args: &Vec<lir::Variable>,
        expected_params: &Vec<BasicMetadataTypeEnum<'ctx>>,
        ray_param_tys: &Vec<Ty>,
        ret_ty: &Ty,
        srcmap: &SourceMap,
    ) -> Result<(CallSiteValue<'ctx>, PointerValue<'ctx>), BuilderError> {
        let (marshalled_vals, ret_slot) =
            self.build_sret_call_args(args, expected_params, ray_param_tys, ret_ty, srcmap)?;

        // Emit the call (returns void in sret case)
        let call = self
            .builder
            .build_call(function, marshalled_vals.as_slice(), "")?;

        // Return the call value and the ret_slot pointer.
        Ok((call, ret_slot))
    }

    /// Build an indirect call
    pub(crate) fn build_indirect_call(
        &mut self,
        func_ptr: PointerValue<'ctx>,
        args: &Vec<lir::Variable>,
        param_tys: &Vec<Ty>,
        ret_ty: &Ty,
        srcmap: &SourceMap,
    ) -> Result<(CallSiteValue<'ctx>, Option<PointerValue<'ctx>>), BuilderError> {
        let llvm_fn_ty = self.to_llvm_fn_ty(param_tys, ret_ty);
        let expected_params: Vec<BasicMetadataTypeEnum<'ctx>> = llvm_fn_ty
            .get_param_types()
            .iter()
            .map(|t| (*t).into())
            .collect();

        if ret_ty.is_aggregate() {
            let (args, ret_slot) =
                self.build_sret_call_args(args, &expected_params, param_tys, ret_ty, srcmap)?;
            let call = self
                .builder
                .build_indirect_call(llvm_fn_ty, func_ptr, &args, "")?;
            return Ok((call, Some(ret_slot)));
        }

        let args = self.build_call_args(args, &expected_params, param_tys, srcmap)?;
        let call = self
            .builder
            .build_indirect_call(llvm_fn_ty, func_ptr, &args, "")?;
        Ok((call, None))
    }
}
