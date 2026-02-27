use inkwell::{
    AddressSpace, IntPredicate,
    builder::BuilderError,
    types::StructType,
    values::{BasicValueEnum, IntValue, PointerValue},
};

use crate::codegen::llvm::context::{LLVMCodegenCtx, MAX_TRACE_DEPTH};

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    /// Returns the LLVM type for a single stack trace entry: `{ ptr, ptr, i32 }`.
    ///
    /// Layout: function_name (null-terminated C string), file (null-terminated C string), line.
    pub(crate) fn trace_entry_type(&self) -> StructType<'ctx> {
        let ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let i32_ty = self.lcx.i32_type();
        self.lcx.struct_type(
            &[ptr_ty.into(), ptr_ty.into(), i32_ty.into(), i32_ty.into()],
            false,
        )
    }

    /// Returns the LLVM type for the thread-local panic/recover context.
    ///
    /// Layout:
    /// - field 0: `bool` — unwinding flag
    /// - field 1: `{ ptr, uint, uint }` — panic message (Ray string)
    /// - field 2: `i32` — trace entry count
    /// - field 3: `[TraceEntry; MAX_TRACE_DEPTH]` — stack trace entries
    pub(crate) fn thread_context_type(&self) -> StructType<'ctx> {
        let bool_ty = self.lcx.bool_type();
        // string = { raw_ptr: rawptr[u8], len: uint, char_len: uint }
        let raw_ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let uint_ty = self.ptr_type();
        let string_ty = self
            .lcx
            .struct_type(&[raw_ptr_ty.into(), uint_ty.into(), uint_ty.into()], false);
        let i32_ty = self.lcx.i32_type();
        let trace_entry_ty = self.trace_entry_type();
        let trace_array_ty = trace_entry_ty.array_type(MAX_TRACE_DEPTH);
        self.lcx.struct_type(
            &[
                bool_ty.into(),
                string_ty.into(),
                i32_ty.into(),
                trace_array_ty.into(),
            ],
            false,
        )
    }

    pub(crate) fn get_thread_ctx_ptr(&self) -> PointerValue<'ctx> {
        self.thread_ctx
            .expect("thread context global not initialized")
    }

    pub(crate) fn load_unwinding_flag(&mut self) -> Result<IntValue<'ctx>, BuilderError> {
        let ptr = self.get_thread_ctx_ptr();
        let ctx_ty = self.thread_context_type();
        let flag_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ptr, 0, "unwinding_ptr")?;
        let flag = self
            .builder
            .build_load(self.lcx.bool_type(), flag_ptr, "unwinding")?;
        Ok(flag.into_int_value())
    }

    pub(crate) fn store_unwinding_flag(&mut self, val: IntValue<'ctx>) -> Result<(), BuilderError> {
        let ptr = self.get_thread_ctx_ptr();
        let ctx_ty = self.thread_context_type();
        let flag_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ptr, 0, "unwinding_ptr")?;
        self.builder.build_store(flag_ptr, val)?;
        Ok(())
    }

    pub(crate) fn load_panic_message(&mut self) -> Result<BasicValueEnum<'ctx>, BuilderError> {
        let ptr = self.get_thread_ctx_ptr();
        let ctx_ty = self.thread_context_type();
        let msg_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ptr, 1, "panic_msg_ptr")?;
        let string_ty = {
            let raw_ptr_ty = self.lcx.ptr_type(AddressSpace::default());
            let uint_ty = self.ptr_type();
            self.lcx
                .struct_type(&[raw_ptr_ty.into(), uint_ty.into(), uint_ty.into()], false)
        };
        let msg = self.builder.build_load(string_ty, msg_ptr, "panic_msg")?;
        Ok(msg)
    }

    pub(crate) fn store_panic_message(
        &mut self,
        msg: BasicValueEnum<'ctx>,
    ) -> Result<(), BuilderError> {
        let ptr = self.get_thread_ctx_ptr();
        let ctx_ty = self.thread_context_type();
        let msg_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ptr, 1, "panic_msg_ptr")?;
        self.builder.build_store(msg_ptr, msg)?;
        Ok(())
    }

    /// Pushes a stack trace entry if `trace_count < MAX_TRACE_DEPTH`.
    ///
    /// Emits: load count, bounds check, GEP into entries[count], store fields, increment count.
    pub(crate) fn push_trace_entry(
        &mut self,
        fn_name_ptr: PointerValue<'ctx>,
        file_ptr: PointerValue<'ctx>,
        line: IntValue<'ctx>,
        col: IntValue<'ctx>,
    ) -> Result<(), BuilderError> {
        let i32_ty = self.lcx.i32_type();
        let ctx_ptr = self.get_thread_ctx_ptr();
        let ctx_ty = self.thread_context_type();

        // Load trace_count (field 2).
        let count_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ctx_ptr, 2, "trace_count_ptr")?;
        let count = self
            .builder
            .build_load(i32_ty, count_ptr, "trace_count")?
            .into_int_value();

        // Bounds check: if count >= MAX_TRACE_DEPTH, skip.
        let max_depth = i32_ty.const_int(MAX_TRACE_DEPTH as u64, false);
        let is_full =
            self.builder
                .build_int_compare(IntPredicate::UGE, count, max_depth, "trace_full")?;

        let current_fn = self.curr_fn.unwrap();
        let push_bb = self.lcx.append_basic_block(current_fn, "trace_push");
        let merge_bb = self.lcx.append_basic_block(current_fn, "trace_merge");
        self.builder
            .build_conditional_branch(is_full, merge_bb, push_bb)?;

        // Push block: store the entry and increment count.
        self.builder.position_at_end(push_bb);

        // GEP into trace_entries[count].
        let entry_ty = self.trace_entry_type();
        let entries_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ctx_ptr, 3, "trace_entries_ptr")?;
        let entry_ptr = unsafe {
            self.builder
                .build_gep(entry_ty, entries_ptr, &[count], "trace_entry_ptr")?
        };

        // Store fn_name (field 0), file (field 1), line (field 2).
        let fn_name_field =
            self.builder
                .build_struct_gep(entry_ty, entry_ptr, 0, "entry.fn_name")?;
        self.builder.build_store(fn_name_field, fn_name_ptr)?;

        let file_field = self
            .builder
            .build_struct_gep(entry_ty, entry_ptr, 1, "entry.file")?;
        self.builder.build_store(file_field, file_ptr)?;

        let line_field = self
            .builder
            .build_struct_gep(entry_ty, entry_ptr, 2, "entry.line")?;
        self.builder.build_store(line_field, line)?;

        let col_field = self
            .builder
            .build_struct_gep(entry_ty, entry_ptr, 3, "entry.col")?;
        self.builder.build_store(col_field, col)?;

        // Increment trace_count.
        let one = i32_ty.const_int(1, false);
        let new_count = self.builder.build_int_add(count, one, "trace_count_inc")?;
        self.builder.build_store(count_ptr, new_count)?;

        self.builder.build_unconditional_branch(merge_bb)?;

        // Continue from merge.
        self.builder.position_at_end(merge_bb);
        Ok(())
    }

    /// Print the full stack trace to stderr.
    ///
    /// Format per entry: `  at <fn_name> (<file>:<line>:<col>)\n`
    pub(crate) fn print_trace(&mut self) -> Result<(), BuilderError> {
        let i32_ty = self.lcx.i32_type();
        let ptr_ty = self.lcx.ptr_type(AddressSpace::default());
        let current_fn = self.curr_fn.unwrap();
        let ctx_ptr = self.get_thread_ctx_ptr();
        let ctx_ty = self.thread_context_type();
        let entry_ty = self.trace_entry_type();

        // Load trace_count.
        let count_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ctx_ptr, 2, "pt.count_ptr")?;
        let count = self
            .builder
            .build_load(i32_ty, count_ptr, "pt.count")?
            .into_int_value();

        // Entries base pointer.
        let entries_ptr = self
            .builder
            .build_struct_gep(ctx_ty, ctx_ptr, 3, "pt.entries_ptr")?;

        // Loop index.
        let idx_alloca = self.builder.build_alloca(i32_ty, "pt.idx")?;
        self.builder.build_store(idx_alloca, i32_ty.const_zero())?;

        let loop_bb = self.lcx.append_basic_block(current_fn, "pt.loop");
        let body_bb = self.lcx.append_basic_block(current_fn, "pt.body");
        let done_bb = self.lcx.append_basic_block(current_fn, "pt.done");
        self.builder.build_unconditional_branch(loop_bb)?;

        // Loop header: check idx < count.
        self.builder.position_at_end(loop_bb);
        let idx = self
            .builder
            .build_load(i32_ty, idx_alloca, "pt.i")?
            .into_int_value();
        let in_bounds = self
            .builder
            .build_int_compare(IntPredicate::ULT, idx, count, "pt.cmp")?;
        self.builder
            .build_conditional_branch(in_bounds, body_bb, done_bb)?;

        // Body: print one trace entry.
        self.builder.position_at_end(body_bb);

        // GEP to entries[idx].
        let entry_ptr = unsafe {
            self.builder
                .build_gep(entry_ty, entries_ptr, &[idx], "pt.entry")?
        };

        // Load fields.
        let fn_name_ptr = self
            .builder
            .build_struct_gep(entry_ty, entry_ptr, 0, "pt.fn_ptr")?;
        let fn_name = self
            .builder
            .build_load(ptr_ty, fn_name_ptr, "pt.fn")?
            .into_pointer_value();
        let file_ptr_field =
            self.builder
                .build_struct_gep(entry_ty, entry_ptr, 1, "pt.file_ptr")?;
        let file = self
            .builder
            .build_load(ptr_ty, file_ptr_field, "pt.file")?
            .into_pointer_value();
        let line_ptr = self
            .builder
            .build_struct_gep(entry_ty, entry_ptr, 2, "pt.line_ptr")?;
        let line = self
            .builder
            .build_load(i32_ty, line_ptr, "pt.line")?
            .into_int_value();
        let col_ptr = self
            .builder
            .build_struct_gep(entry_ty, entry_ptr, 3, "pt.col_ptr")?;
        let col = self
            .builder
            .build_load(i32_ty, col_ptr, "pt.col")?
            .into_int_value();

        // Print: "  at "
        let at_global = self.create_cstring_global("  at ", "trace.at");
        self.write_stderr(at_global.as_pointer_value(), i32_ty.const_int(5, false))?;

        // Print: fn_name
        self.write_stderr_cstr(fn_name)?;

        // Print: " ("
        let paren_open = self.create_cstring_global(" (", "trace.paren_open");
        self.write_stderr(paren_open.as_pointer_value(), i32_ty.const_int(2, false))?;

        // Print: file
        self.write_stderr_cstr(file)?;

        // Print: ":"
        let colon = self.create_cstring_global(":", "trace.colon");
        self.write_stderr(colon.as_pointer_value(), i32_ty.const_int(1, false))?;

        // Print: line
        self.write_stderr_i32(line)?;

        // Print: ":"
        self.write_stderr(colon.as_pointer_value(), i32_ty.const_int(1, false))?;

        // Print: col
        self.write_stderr_i32(col)?;

        // Print: ")\n"
        let paren_close = self.create_cstring_global(")\n", "trace.paren_close");
        self.write_stderr(paren_close.as_pointer_value(), i32_ty.const_int(2, false))?;

        // Increment index and loop.
        let next_idx = self
            .builder
            .build_int_add(idx, i32_ty.const_int(1, false), "pt.next")?;
        self.builder.build_store(idx_alloca, next_idx)?;
        self.builder.build_unconditional_branch(loop_bb)?;

        self.builder.position_at_end(done_bb);
        Ok(())
    }
}
