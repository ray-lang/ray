use inkwell::{
    AddressSpace,
    builder::BuilderError,
    values::{IntValue, PointerValue},
};

use crate::codegen::llvm::context::LLVMCodegenCtx;

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    /// Write `len` bytes starting at `ptr` to stderr (fd=2) via WASI `fd_write`.
    pub(crate) fn write_stderr(
        &mut self,
        ptr: PointerValue<'ctx>,
        len: IntValue<'ctx>,
    ) -> Result<(), BuilderError> {
        let i32_ty = self.lcx.i32_type();
        let fd_write_fn = self.get_or_declare_fd_write();

        // Build an IOVec { base: ptr, len: len } on the stack.
        let iov_ty = self.lcx.struct_type(
            &[
                self.lcx.ptr_type(AddressSpace::default()).into(),
                i32_ty.into(),
            ],
            false,
        );
        let iov_alloca = self.builder.build_alloca(iov_ty, "iov")?;
        let base_ptr = self
            .builder
            .build_struct_gep(iov_ty, iov_alloca, 0, "iov.base")?;
        self.builder.build_store(base_ptr, ptr)?;
        let len_ptr = self
            .builder
            .build_struct_gep(iov_ty, iov_alloca, 1, "iov.len")?;
        self.builder.build_store(len_ptr, len)?;

        // nwritten output (we ignore the result).
        let nwritten_alloca = self.builder.build_alloca(i32_ty, "nwritten")?;

        // fd_write(2, &iov, 1, &nwritten)
        let fd = i32_ty.const_int(2, false);
        let one = i32_ty.const_int(1, false);
        self.builder.build_call(
            fd_write_fn,
            &[
                fd.into(),
                iov_alloca.into(),
                one.into(),
                nwritten_alloca.into(),
            ],
            "fd_write_ret",
        )?;
        Ok(())
    }

    /// Write a null-terminated C string (pointed to by `cstr_ptr`) to stderr.
    pub(crate) fn write_stderr_cstr(
        &mut self,
        cstr_ptr: PointerValue<'ctx>,
    ) -> Result<(), BuilderError> {
        let strlen_fn = self.get_or_declare_strlen();
        let len = self
            .builder
            .build_call(strlen_fn, &[cstr_ptr.into()], "strlen")?
            .try_as_basic_value()
            .unwrap_basic()
            .into_int_value();
        self.write_stderr(cstr_ptr, len)?;
        Ok(())
    }

    /// Write an i32 value as a decimal string to stderr.
    pub(crate) fn write_stderr_i32(&mut self, val: IntValue<'ctx>) -> Result<(), BuilderError> {
        let i32_ty = self.lcx.i32_type();
        let i8_ty = self.lcx.i8_type();

        let buf_size = 12u32;
        let buf_ty = i8_ty.array_type(buf_size);
        let buf_alloca = self.builder.build_alloca(buf_ty, "itoa.buf")?;
        let buf_len = i32_ty.const_int(buf_size as u64, false);

        let itoa_fn = self.get_or_declare_itoa();
        let start_ptr = self
            .builder
            .build_call(
                itoa_fn,
                &[val.into(), buf_alloca.into(), buf_len.into()],
                "itoa",
            )?
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();

        let strlen_fn = self.get_or_declare_strlen();
        let written_len = self
            .builder
            .build_call(strlen_fn, &[start_ptr.into()], "itoa.len")?
            .try_as_basic_value()
            .unwrap_basic()
            .into_int_value();

        self.write_stderr(start_ptr, written_len)?;
        Ok(())
    }
}
