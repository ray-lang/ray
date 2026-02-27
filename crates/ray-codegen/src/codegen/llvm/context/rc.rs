use inkwell::{
    builder::BuilderError,
    values::{IntValue, PointerValue},
};
use ray_lir::RefCountKind;

use crate::codegen::llvm::context::LLVMCodegenCtx;

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    /// Size of the refcount header in bytes: `2 * sizeof(ptr)`.
    /// Layout: `[strong_count: uint | weak_count: uint | data: T]`
    pub(crate) fn rc_header_size(&self) -> Result<IntValue<'ctx>, BuilderError> {
        let ptr_size =
            self.builder
                .build_int_cast(self.ptr_type().size_of(), self.ptr_type(), "ptr_size")?;
        let two = self.ptr_type().const_int(2, false);
        Ok(self.builder.build_int_mul(ptr_size, two, "rc_header")?)
    }

    /// Given a data pointer (past the refcount header), compute the allocation
    /// base pointer by subtracting the header size.
    pub(crate) fn get_rc_base_ptr(
        &self,
        data_ptr: PointerValue<'ctx>,
    ) -> Result<PointerValue<'ctx>, BuilderError> {
        let header_size = self.rc_header_size()?;
        let neg_header = self.builder.build_int_neg(header_size, "neg_header")?;
        unsafe {
            self.builder
                .build_gep(self.lcx.i8_type(), data_ptr, &[neg_header], "rc_base")
        }
    }

    /// Get a pointer to the strong or weak count field given the allocation base pointer.
    /// `kind == Strong` → offset 0 (strong_count), `kind == Weak` → offset 1 (weak_count).
    pub(crate) fn get_rc_count_ptr(
        &self,
        base_ptr: PointerValue<'ctx>,
        kind: RefCountKind,
    ) -> Result<PointerValue<'ctx>, BuilderError> {
        let offset = match kind {
            RefCountKind::Strong => self.ptr_type().const_int(0, false),
            RefCountKind::Weak => self.ptr_type().const_int(1, false),
        };
        unsafe {
            self.builder
                .build_gep(self.ptr_type(), base_ptr, &[offset], "rc_count_ptr")
        }
    }

    /// Compute the total allocation size and alignment for a refcounted object
    /// whose data pointer is `data_ptr`. Uses the registered pointee type.
    pub(crate) fn rc_alloc_layout(
        &mut self,
        data_ptr: PointerValue<'ctx>,
    ) -> Result<(IntValue<'ctx>, IntValue<'ctx>), BuilderError> {
        let pointee_ty = self.get_pointee_ty(data_ptr).clone();
        let llvm_ty = self.to_llvm_type(&pointee_ty);
        let header_size = self.rc_header_size()?;
        let data_size = self.llvm_size_of(llvm_ty, "data_size")?;
        let total_size = self
            .builder
            .build_int_add(header_size, data_size, "dealloc_size")?;
        let td = self.target_machine.get_target_data();
        let align = td.get_abi_alignment(&llvm_ty);
        let align_val = self.ptr_type().const_int(align as u64, false);
        Ok((total_size, align_val))
    }
}
