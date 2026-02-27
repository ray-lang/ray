use inkwell::{AddressSpace, module::Linkage, values::FunctionValue};
use ray_shared::ty::Ty;

use crate::codegen::llvm::context::LLVMCodegenCtx;

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    pub(crate) fn ensure_wasi_globals(&mut self) {
        let i32_ty = self.lcx.i32_type();
        for name in ["__heap_base", "__heap_end"] {
            if self.module.get_global(name).is_some() {
                continue;
            }
            let global = self
                .module
                .add_global(i32_ty, Some(AddressSpace::default()), name);
            global.set_linkage(Linkage::External);

            let ptr = global.as_pointer_value();
            self.register_pointee_ty(ptr, Ty::i32());
        }
    }

    /// Declare `__wasi_alloc(size: i32, align: i32) -> ptr`.
    pub(crate) fn get_or_declare_alloc(&self) -> FunctionValue<'ctx> {
        if let Some(f) = self.module.get_function("__wasi_alloc") {
            return f;
        }
        let ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let size_ty = self.ptr_type();
        let fn_ty = ptr_ty.fn_type(&[size_ty.into(), size_ty.into()], false);
        self.module
            .add_function("__wasi_alloc", fn_ty, Some(Linkage::External))
    }

    /// Declare `__wasi_dealloc(ptr: ptr, size: i32, align: i32) -> void`.
    pub(crate) fn get_or_declare_dealloc(&self) -> FunctionValue<'ctx> {
        if let Some(f) = self.module.get_function("__wasi_dealloc") {
            return f;
        }
        let void_ty = self.lcx.void_type();
        let ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let size_ty = self.ptr_type();
        let fn_ty = void_ty.fn_type(&[ptr_ty.into(), size_ty.into(), size_ty.into()], false);
        self.module
            .add_function("__wasi_dealloc", fn_ty, Some(Linkage::External))
    }

    /// Declare `strlen(ptr) -> i32` (provided by wasi_builtins).
    pub(crate) fn get_or_declare_strlen(&self) -> FunctionValue<'ctx> {
        if let Some(f) = self.module.get_function("strlen") {
            return f;
        }
        let i32_ty = self.lcx.i32_type();
        let ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let fn_ty = i32_ty.fn_type(&[ptr_ty.into()], false);
        self.module
            .add_function("strlen", fn_ty, Some(Linkage::External))
    }

    /// Declare `__wasi_itoa(val, buf, buf_len) -> ptr` (provided by wasi_builtins).
    pub(crate) fn get_or_declare_itoa(&self) -> FunctionValue<'ctx> {
        if let Some(f) = self.module.get_function("__wasi_itoa") {
            return f;
        }
        let i32_ty = self.lcx.i32_type();
        let ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let fn_ty = ptr_ty.fn_type(&[i32_ty.into(), ptr_ty.into(), i32_ty.into()], false);
        self.module
            .add_function("__wasi_itoa", fn_ty, Some(Linkage::External))
    }

    /// Declare WASI `fd_write(fd, iovs, iovs_len, nwritten) -> i32` import.
    pub(crate) fn get_or_declare_fd_write(&self) -> FunctionValue<'ctx> {
        if let Some(f) = self.module.get_function("fd_write") {
            return f;
        }
        let i32_ty = self.lcx.i32_type();
        let ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let fn_ty = i32_ty.fn_type(
            &[i32_ty.into(), ptr_ty.into(), i32_ty.into(), ptr_ty.into()],
            false,
        );
        let f = self
            .module
            .add_function("fd_write", fn_ty, Some(Linkage::External));
        self.fn_attr(f, "wasm-import-module", "wasi_snapshot_preview1");
        self.fn_attr(f, "wasm-import-name", "fd_write");
        f
    }
}
