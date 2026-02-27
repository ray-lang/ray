mod attr;
mod context;

use std::{
    collections::{HashMap, hash_map::Entry},
    env::{self, temp_dir},
    fs,
    io::Write,
    ops::Deref,
    ptr,
};

use inkwell::{
    self as llvm, builder::BuilderError, passes::PassBuilderOptions, types::BasicType as _,
};
use llvm::{
    AddressSpace, IntPredicate,
    module::Linkage,
    targets::FileType,
    types::BasicTypeEnum,
    values::{
        BasicValue, BasicValueEnum, CallSiteValue, InstructionOpcode, InstructionValue, IntValue,
        PointerValue, ValueKind,
    },
};
use rand::RngCore;
use ray_core::{
    ast::Modifier,
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
    target::Target,
};
use ray_lir::{self as lir, SymbolSet};
use ray_shared::{
    optlevel::OptLevel,
    pathlib::{FilePath, Path},
    ty::Ty,
    utils::map_join,
};
use ray_typing::types::{Subst, Substitutable as _};

use crate::codegen::{Codegen, CodegenOptions, collect_symbols, llvm::context::LLVMCodegenCtx};

/// Extension trait for codegen methods on lir::Call
trait CallCodegenExt<'a, 'ctx> {
    fn codegen_intrinsic(
        &self,
        kind: lir::IntrinsicKind,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
    ) -> Result<LoweredCall<'ctx>, BuilderError>;

    fn codegen_ptr_offset(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
        is_add: bool,
    ) -> Result<LoweredCall<'ctx>, BuilderError>;

    fn codegen_deref(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
    ) -> Result<LoweredCall<'ctx>, BuilderError>;

    fn codegen_sizeof(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
    ) -> Result<LoweredCall<'ctx>, BuilderError>;

    fn codegen_basic_op(
        &self,
        op: lir::Op,
        signed: bool,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
    ) -> Result<LoweredCall<'ctx>, BuilderError>;

    fn eval_intrinsic_ptr(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
        idx: usize,
    ) -> Result<PointerValue<'ctx>, BuilderError>;

    fn eval_intrinsic_int(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
        idx: usize,
    ) -> Result<IntValue<'ctx>, BuilderError>;
}

static BUILTINS_BUF: &'static [u8] =
    include_bytes!("../../../../../lib/wasi_builtins/wasi_builtins.wasm");

lazy_static! {
    static ref BUILTINS_BUF_HASH: u64 = xxhash_rust::xxh3::xxh3_64(BUILTINS_BUF);
}

pub fn codegen<P>(
    program: &lir::Program,
    srcmap: &SourceMap,
    target: &Target,
    output_path: P,
    options: CodegenOptions,
) -> Result<(), Vec<RayError>>
where
    P: FnOnce(&'static str) -> FilePath,
{
    let lcx = llvm::context::Context::create();
    let name = program.module_path.to_string();
    let module = lcx.create_module(&name);
    let builder = lcx.create_builder();
    let mut ctx = LLVMCodegenCtx::new(
        target,
        &lcx,
        &module,
        &builder,
        &program.struct_types,
        &program.enum_types,
    );
    if let Some(err) = program.codegen(&mut ctx, srcmap).err() {
        // TODO: convert to ray error
        panic!("error during codegen: {}", err);
    }
    ctx.ensure_wasi_globals();

    if let Err(err) = module.verify() {
        panic!(
            "COMPILER BUG: {}\n{}",
            err.to_string(),
            module.print_to_string().to_string()
        );
    }

    log::debug!(
        "LLVM Module (BEFORE PASSES):\n--------------\n{}",
        module.print_to_string().to_string()
    );

    // TODO: handle optimization level
    let pass_options = PassBuilderOptions::create();

    // always-inline
    // function passes:
    //   - mem2reg
    //   - sroa (breaks up allocas)
    //   - instcombine, reassociate, gvn, simplifycfg (classic cleanups)
    let passes = match options.opt_level {
        OptLevel::O0 => "",
        OptLevel::O1 => "default<O1>",
        OptLevel::O2 => "default<O2>",
        OptLevel::O3 => "default<O3>",
        OptLevel::Os => "default<Os>",
        OptLevel::Oz => "default<Oz>",
    };

    if !passes.is_empty() {
        if let Some(err) = module
            .run_passes(passes, &ctx.target_machine, pass_options)
            .err()
        {
            panic!("error during passes: {}", err);
        }
    }

    if let Err(err) = module.verify() {
        panic!(
            "COMPILER BUG: {}\n{}",
            err.to_string(),
            module.print_to_string().to_string()
        );
    }

    if options.emit {
        println!("{}", module.print_to_string().to_string());
        return Ok(());
    }

    log::debug!(
        "LLVM Module:\n--------------\n{}",
        module.print_to_string().to_string()
    );

    // write out the object to a temp file
    let mut rng = rand::thread_rng();
    let id = rng.next_u64();
    let tmp_dir = FilePath::from(temp_dir());
    let base = format!("{}_{}.ray", name, id);
    let obj_path = tmp_dir.clone() / format!("{}.o", base);
    ctx.target_machine
        .write_to_file(&module, FileType::Object, obj_path.as_ref())
        .unwrap();

    let builtins_path = tmp_dir.clone() / format!("wasi_builtins.{}.a", *BUILTINS_BUF_HASH);
    if !builtins_path.exists() {
        let mut f = fs::File::create(&builtins_path).unwrap();
        f.write_all(BUILTINS_BUF).unwrap();
    }

    let wasm_path = output_path("wasm");
    log::info!("writing to {}", wasm_path);
    let curr_dir = env::current_dir().unwrap();
    if let Some(msg) = lld::link(
        target.to_string(),
        &[
            obj_path.to_string(),
            builtins_path.to_string(),
            str!("--no-entry"),
            str!("-o"),
            curr_dir.join(wasm_path).to_str().unwrap().to_string(),
        ],
    )
    .to_result()
    .err()
    {
        let err = RayError {
            msg,
            src: vec![],
            kind: RayErrorKind::Link,
            context: None,
        };
        return Err(vec![err]);
    }
    Ok(())
}

pub fn emit_module_ir(
    program: &lir::Program,
    srcmap: &SourceMap,
    target: &Target,
    opt_level: OptLevel,
) -> String {
    let context = llvm::context::Context::create();
    let module = context.create_module(&program.module_path.to_string());
    let builder = context.create_builder();
    let mut ctx = LLVMCodegenCtx::new(
        target,
        &context,
        &module,
        &builder,
        &program.struct_types,
        &program.enum_types,
    );
    if let Err(err) = program.codegen(&mut ctx, srcmap) {
        panic!("error during codegen: {}", err);
    }
    ctx.ensure_wasi_globals();

    if let Err(err) = module.verify() {
        panic!(
            "COMPILER BUG: {}\n{}",
            err.to_string(),
            module.print_to_string().to_string()
        );
    }

    let pass_options = PassBuilderOptions::create();
    let passes = match opt_level {
        OptLevel::O0 => "",
        OptLevel::O1 => "default<O1>",
        OptLevel::O2 => "default<O2>",
        OptLevel::O3 => "default<O3>",
        OptLevel::Os => "default<Os>",
        OptLevel::Oz => "default<Oz>",
    };

    if !passes.is_empty() {
        if let Some(err) = module
            .run_passes(passes, &ctx.target_machine, pass_options)
            .err()
        {
            panic!("error during passes: {}", err);
        }
    }

    if let Err(err) = module.verify() {
        panic!(
            "COMPILER BUG: {}\n{}",
            err.to_string(),
            module.print_to_string().to_string()
        );
    }

    module.print_to_string().to_string()
}

// Represents the result of lowering a call in codegen: either a normal callsite (with optional ret slot), or a folded value.
pub(crate) enum LoweredCall<'ctx> {
    Call {
        call: CallSiteValue<'ctx>,
        ret_slot: Option<PointerValue<'ctx>>,
    },
    Value(BasicValueEnum<'ctx>),
    Inst(InstructionValue<'ctx>),
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Program {
    type Output = Result<(), BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        // collect the function symbols
        let mut fn_map: HashMap<Path, &lir::Func> = HashMap::new();
        for func in self.funcs.iter() {
            match fn_map.entry(func.name.clone()) {
                Entry::Vacant(entry) => {
                    entry.insert(func);
                }
                Entry::Occupied(mut entry) => {
                    let existing = *entry.get();
                    let existing_weight = existing.blocks.iter().map(|b| b.len()).sum::<usize>();
                    let new_weight = func.blocks.iter().map(|b| b.len()).sum::<usize>();
                    let existing_symbols = existing.symbols.len();
                    let new_symbols = func.symbols.len();
                    if new_weight > existing_weight
                        || (new_weight == existing_weight && new_symbols > existing_symbols)
                    {
                        entry.insert(func);
                    }
                }
            }
        }
        log::debug!("fn_map: {:#?}", fn_map.keys());

        let mut symbols = SymbolSet::new();
        let start_fn = &self.funcs[self.start_idx as usize];
        symbols.insert(start_fn.name.clone());
        collect_symbols(start_fn, &mut symbols, &fn_map);
        log::debug!("all symbols: {:?}", symbols);

        for ext in self.externs.iter() {
            if !symbols.contains(&ext.name) {
                continue;
            }

            if ext.is_intrinsic {
                let kind = ext
                    .intrinsic_kind
                    .expect("intrinsic extern missing kind metadata");
                ctx.intrinsics.insert(ext.name.clone(), kind);
                log::debug!("insert intrinsic: {} (kind = {:?})", ext.name, kind);
                continue;
            }

            // define
            log::debug!("define extern: {:?}", ext);
            if let Some((_, _, param_tys, ret_ty)) = ext.ty.try_borrow_fn() {
                let fn_ty = ctx.to_llvm_fn_ty(param_tys, ret_ty);
                let name = ext.name.to_string();
                let fn_val = ctx.module.add_function(&name, fn_ty, None);

                if ext.modifiers.contains(&Modifier::Wasi) {
                    ctx.fn_attr(fn_val, "wasm-import-module", "wasi_snapshot_preview1");
                    ctx.fn_attr(fn_val, "wasm-import-name", &name);
                }

                ctx.fn_index.insert(ext.name.clone(), fn_val);
            }
        }

        let i8_type = ctx.lcx.i8_type();
        for d in self.data.iter() {
            let value = d.value();
            let global = ctx.module.add_global(
                i8_type.array_type(value.len() as u32),
                Some(AddressSpace::default()),
                &d.name(),
            );
            global.set_initializer(
                &i8_type.const_array(
                    d.value()
                        .into_iter()
                        .map(|i| i8_type.const_int(i as u64, false))
                        .collect::<Vec<_>>()
                        .as_slice(),
                ),
            );

            let ptr = global.as_pointer_value();
            ctx.register_pointee_ty(ptr, Ty::i8());
            ctx.data_addrs.insert(d.key(), global);
        }

        // Inject the compiler-internal panic/recover thread context global.
        let ctx_ty = ctx.thread_context_type();
        let ctx_global =
            ctx.module
                .add_global(ctx_ty, Some(AddressSpace::default()), "__thread_ctx");
        ctx_global.set_initializer(&ctx_ty.const_zero());
        ctx_global.set_linkage(Linkage::Internal);
        ctx.thread_ctx = Some(ctx_global.as_pointer_value());

        for global in self.globals.iter() {
            let global_type = ctx.to_llvm_type(global.ty.mono());
            let global_val =
                ctx.module
                    .add_global(global_type, Some(AddressSpace::default()), &global.name);
            let init_value = global.init_value.codegen(ctx, srcmap)?;
            global_val.set_initializer(&init_value);

            let ptr = global_val.as_pointer_value();
            ctx.register_pointee_ty(ptr, global.ty.mono().clone());
            ctx.globals.insert(global.key(), global_val);
        }

        let mut funcs = vec![];
        for (i, f) in self.funcs.iter().enumerate() {
            if !symbols.contains(&f.name) {
                // don't generate functions that are not in the symbol set
                continue;
            }

            if let Some(selected) = fn_map.get(&f.name) {
                if !ptr::eq(*selected, f) {
                    continue;
                }
            }

            let (_, _, param_tys, ret_ty) = f.ty.try_borrow_fn().unwrap();
            let param_desc = param_tys
                .iter()
                .map(|ty| ty.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            log::debug!("llvm fn sig {} :: ({}) -> {}", f.name, param_desc, ret_ty);
            let fn_ty = ctx.to_llvm_fn_ty(param_tys, ret_ty);
            log::debug!(
                "  llvm fn type result: {}",
                fn_ty.print_to_string().to_string()
            );
            let name = if f.name == lir::START_FUNCTION {
                "_start".to_string()
            } else {
                f.name.to_mangled()
            };
            let fn_val = ctx.module.add_function(&name, fn_ty, None);
            log::debug!(
                "  added function {} with llvm type {}",
                name,
                fn_val.get_type().print_to_string().to_string()
            );
            if f.modifiers.contains(&Modifier::Wasi) {
                ctx.fn_attr(fn_val, "wasm-import-module", "wasi_snapshot_preview1");
                ctx.fn_attr(fn_val, "wasm-import-name", &name);
            }

            if f.name != lir::START_FUNCTION {
                fn_val.set_linkage(Linkage::Internal);
            } else {
                ctx.fn_attr(fn_val, "wasm-export-name", lir::START_FUNCTION);
            }

            // if srcmap.has_inline(f) {
            //     let inline_attr = ctx
            //         .lcx
            //         .create_enum_attribute(Attribute::get_named_enum_kind_id("alwaysinline"), 0);
            //     fn_val.add_attribute(AttributeLoc::Function, inline_attr);
            // }

            ctx.fn_index.insert(f.name.clone(), fn_val);
            funcs.push((i, fn_val));
        }

        for (i, val) in funcs {
            let f = &self.funcs[i];
            if let Some(selected) = fn_map.get(&f.name) {
                if !ptr::eq(*selected, f) {
                    continue;
                }
            }

            let local_tys = f
                .locals
                .iter()
                .map(|loc| loc.ty.mono().clone())
                .collect::<Vec<_>>();
            ctx.local_tys = local_tys;
            ctx.curr_fn = Some(val);
            f.codegen(ctx, srcmap)?;
        }

        // Bridge `malloc(size) -> ptr` to `__wasi_alloc(size, align=1) -> ptr`.
        // Ray's core library declares `extern fn malloc(size: uint) -> rawptr[u8]`
        // but the WASI allocator exports `__wasi_alloc`. Emit a thin wrapper so
        // the linker resolves the `malloc` symbol.
        if let Some(malloc_fn) = ctx.module.get_function("malloc") {
            if malloc_fn.count_basic_blocks() == 0 {
                let alloc_fn = ctx.get_or_declare_alloc();
                let entry = ctx.lcx.append_basic_block(malloc_fn, "entry");
                ctx.builder.position_at_end(entry);
                let size_arg = malloc_fn.get_first_param().unwrap().into_int_value();
                let align = ctx.ptr_type().const_int(1, false);
                let result = ctx
                    .builder
                    .build_call(alloc_fn, &[size_arg.into(), align.into()], "ptr")?
                    .try_as_basic_value()
                    .unwrap_basic();
                ctx.builder.build_return(Some(&result))?;
            }
        }

        Ok(())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Func {
    type Output = Result<(), BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        log::debug!("generating {}", self);
        // clear the locals and blocks
        ctx.locals.clear();
        ctx.blocks.clear();

        // create the local types
        ctx.local_tys = self
            .locals
            .iter()
            .map(|l| l.ty.clone().into_mono())
            .collect();

        // create the function value
        let fn_val = *ctx.fn_index.get(&self.name).unwrap();
        let ret_ty: &Ty = self.ty.mono().get_fn_ret_ty().unwrap();
        ctx.curr_fn = Some(fn_val);
        ctx.curr_ret_ty = Some(ret_ty.clone());
        ctx.fn_index.insert(self.name.clone(), fn_val);
        ctx.sret_param = None;

        // initialize the entry block with arguments
        let entry = ctx.lcx.append_basic_block(fn_val, "entry");
        ctx.builder.position_at_end(entry);

        let mut params_iter = fn_val.get_param_iter();
        if ret_ty.is_aggregate() {
            // First LLVM param is the sret pointer
            if let Some(retptr_val) = params_iter.next() {
                let retptr = retptr_val.into_pointer_value();
                ctx.sret_param = Some(retptr);
                ctx.register_pointee_ty(retptr, ret_ty.clone());
            }
        }
        for (param_val, param) in params_iter.zip(self.params.iter()) {
            param_val.set_name(&param.name);
            if let Ty::Var(v) = &param.ty {
                if v.is_unknown() {
                    panic!(
                        "cannot codegen function `{}`: param `${}` has unresolved type variable `{}` ({})",
                        self.name, param.idx, v, param.ty
                    );
                }
            }
            let alloca = ctx.alloca(&param.ty)?;
            ctx.builder.build_store(alloca, param_val)?;
            ctx.locals.insert(param.idx, alloca);
        }

        for loc in self.locals.iter() {
            if loc.idx < self.params.len() {
                continue;
            }

            let ty = loc.ty.mono();
            // Skip compile-time meta-type locals (e.g., type['a])
            if ty.is_meta_ty() {
                continue;
            }
            if let Ty::Var(v) = ty {
                if v.is_unknown() {
                    let defining_inst = self.blocks.iter().flat_map(|block| block.iter()).find_map(
                        |inst| match inst {
                            lir::Inst::SetLocal(idx, value) if *idx == loc.idx => {
                                let mut msg =
                                    format!("{}", lir::FuncDisplayCtx::new(inst, &self.locals));
                                if let lir::Value::Call(call) = value {
                                    if let Some(src) = &call.source {
                                        msg.push_str(&format!(" @ {:?}", src));
                                    }
                                }
                                Some(msg)
                            }
                            _ => None,
                        },
                    );
                    panic!(
                        "cannot codegen function `{}`: local `${}` has unresolved type variable `{}` ({}){}",
                        self.name,
                        loc.idx,
                        v,
                        loc.ty,
                        defining_inst
                            .as_ref()
                            .map(|s| format!("\nfirst defining inst: {}", s))
                            .unwrap_or_default()
                    );
                }
            }

            let alloca = ctx.alloca(ty)?;
            ctx.locals.insert(loc.idx, alloca);
        }

        // codegen each block as a basic block
        for block in self.blocks.iter() {
            let bb = ctx.get_block(block.label());
            ctx.builder.position_at_end(bb);
            block.codegen(ctx, srcmap)?;
        }

        // add a branch from entry block to first block
        if let Some(first_block) = self.blocks.first() {
            let dest = ctx.get_block(first_block.label());
            ctx.builder.position_at_end(entry);
            ctx.builder.build_unconditional_branch(dest)?;
        }

        Ok(())
    }
}

impl Codegen<LLVMCodegenCtx<'_, '_>> for lir::Block {
    type Output = Result<(), BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'_, '_>, srcmap: &SourceMap) -> Self::Output {
        for i in self.deref() {
            let _ = i.codegen(ctx, srcmap)?;

            // use inkwell::values::InstructionOpcode::*;
            // if matches!(
            //     iv.get_opcode(),
            //     Return | Br | Switch | IndirectBr | Resume | Unreachable
            // ) {
            //     saw_term = true;
            //     // warn if more instructions remain in this block
            //     if let Some(next) = self
            //         .deref()
            //         .iter()
            //         .skip_while(|i| !ptr::eq(*i, inst))
            //         .nth(1)
            //     {
            //         log::warn!("Dead code after terminator: {:?}", next);
            //     }
            //     break;
            // }
        }

        Ok(())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Inst {
    type Output = Result<Option<InstructionValue<'ctx>>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        log::debug!("[codegen] {}", self);
        Ok(Some(match self {
            lir::Inst::StructInit(_, _) => {
                // Struct locals are value-typed now, so StructInit has no codegen work.
                return Ok(None);
            }

            lir::Inst::Free(local_idx) => {
                // Free a heap allocation. Compute layout from the pointee type,
                // get the allocation base pointer, and call __wasi_dealloc.
                let data_ptr = ctx.load_local(*local_idx)?.into_pointer_value();
                let base_ptr = ctx.get_rc_base_ptr(data_ptr)?;
                let (total_size, align) = ctx.rc_alloc_layout(data_ptr)?;
                let dealloc_fn = ctx.get_or_declare_dealloc();
                ctx.builder
                    .build_call(
                        dealloc_fn,
                        &[base_ptr.into(), total_size.into(), align.into()],
                        "",
                    )?
                    .try_as_basic_value()
                    .expect_instruction("dealloc returns void")
            }
            lir::Inst::Call(call) => {
                match call.codegen(ctx, srcmap)? {
                    LoweredCall::Value(_v) => {
                        // Intrinsic folded to a value in expression position; as a statement call,
                        // this becomes a no-op.
                        return Ok(None);
                    }
                    LoweredCall::Call { call, .. } => match call.try_as_basic_value() {
                        ValueKind::Basic(val) => val.as_instruction_value().unwrap(),
                        ValueKind::Instruction(inst) => inst,
                    },
                    LoweredCall::Inst(inst) => inst,
                }
            }
            lir::Inst::CExternCall(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetGlobal(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetLocal(idx, value) => {
                if ctx.local_tys[*idx].is_meta_ty() {
                    // Meta-typed locals (e.g., type[T]) have no runtime representation.
                    // Their RHS is also a meta expression and must not lower to LLVM at all.
                    // Skipping codegen here avoids spurious loads/stores and keeps IR clean.
                    return Ok(None);
                }
                ctx.build_set_local(*idx, value, srcmap)?
            }
            lir::Inst::MemCopy(dest_var, src_var, size) => {
                ctx.build_memcpy(dest_var, src_var, size, srcmap)?
            }
            lir::Inst::Store(s) => s.codegen(ctx, srcmap)?,
            lir::Inst::Insert(i) => i.codegen(ctx, srcmap)?,
            lir::Inst::SetField(s) => s.codegen(ctx, srcmap)?,
            lir::Inst::IncRef(value, kind) => {
                // Increment the strong or weak reference count by 1.
                // For locals, load the heap pointer from the stack alloca.
                let data_ptr = if let Some(idx) = value.local() {
                    ctx.load_local(idx)?.into_pointer_value()
                } else {
                    value.codegen(ctx, srcmap)?.into_pointer_value()
                };
                let base_ptr = ctx.get_rc_base_ptr(data_ptr)?;
                let count_ptr = ctx.get_rc_count_ptr(base_ptr, *kind)?;

                let count_ty = ctx.ptr_type();
                let old_count = ctx
                    .builder
                    .build_load(count_ty, count_ptr, "rc_load")?
                    .into_int_value();
                let new_count =
                    ctx.builder
                        .build_int_add(old_count, count_ty.const_int(1, false), "rc_inc")?;
                ctx.builder.build_store(count_ptr, new_count)?
            }
            lir::Inst::DecRef(value, kind, drop_fn) => {
                // Decrement the strong or weak reference count by 1.
                // If the count reaches 0, conditionally free the allocation.
                // For strong DecRef with a drop function: call drop glue first.
                // For locals, load the heap pointer from the stack alloca.
                let data_ptr = if let Some(idx) = value.local() {
                    ctx.load_local(idx)?.into_pointer_value()
                } else {
                    value.codegen(ctx, srcmap)?.into_pointer_value()
                };
                let base_ptr = ctx.get_rc_base_ptr(data_ptr)?;
                let count_ptr = ctx.get_rc_count_ptr(base_ptr, *kind)?;

                let count_ty = ctx.ptr_type();
                let old_count = ctx
                    .builder
                    .build_load(count_ty, count_ptr, "rc_load")?
                    .into_int_value();
                let new_count =
                    ctx.builder
                        .build_int_sub(old_count, count_ty.const_int(1, false), "rc_dec")?;
                ctx.builder.build_store(count_ptr, new_count)?;

                // Check if count reached 0
                let is_zero = ctx.builder.build_int_compare(
                    IntPredicate::EQ,
                    new_count,
                    count_ty.const_int(0, false),
                    "rc_is_zero",
                )?;

                let fn_val = ctx.get_fn();
                let then_bb = ctx.lcx.append_basic_block(fn_val, "rc_maybe_free");
                let merge_bb = ctx.lcx.append_basic_block(fn_val, "rc_merge");

                ctx.builder
                    .build_conditional_branch(is_zero, then_bb, merge_bb)?;

                // then block: this count reached 0
                ctx.builder.position_at_end(then_bb);

                // For strong DecRef with a drop function: call it now.
                // The drop function runs the user's destruct() and decrements
                // refcounts of all reference-typed fields.
                if matches!(kind, lir::RefCountKind::Strong) {
                    if let Some(drop_fn_ref) = drop_fn {
                        if let Some(&drop_fn_val) = ctx.fn_index.get(&drop_fn_ref.path) {
                            ctx.builder
                                .build_call(drop_fn_val, &[data_ptr.into()], "")?;
                        }
                    }
                }

                // Check the other count
                let other_kind = match kind {
                    lir::RefCountKind::Strong => lir::RefCountKind::Weak,
                    lir::RefCountKind::Weak => lir::RefCountKind::Strong,
                };
                let other_ptr = ctx.get_rc_count_ptr(base_ptr, other_kind)?;
                let other_count = ctx
                    .builder
                    .build_load(count_ty, other_ptr, "rc_other_load")?
                    .into_int_value();
                let other_is_zero = ctx.builder.build_int_compare(
                    IntPredicate::EQ,
                    other_count,
                    count_ty.const_int(0, false),
                    "rc_other_zero",
                )?;

                let free_bb = ctx.lcx.append_basic_block(fn_val, "rc_free");
                ctx.builder
                    .build_conditional_branch(other_is_zero, free_bb, merge_bb)?;

                // free block: both counts are 0, deallocate
                ctx.builder.position_at_end(free_bb);
                let (total_size, align) = ctx.rc_alloc_layout(data_ptr)?;
                let dealloc_fn = ctx.get_or_declare_dealloc();
                ctx.builder.build_call(
                    dealloc_fn,
                    &[base_ptr.into(), total_size.into(), align.into()],
                    "",
                )?;
                ctx.builder.build_unconditional_branch(merge_bb)?;

                // continue at merge block
                ctx.builder.position_at_end(merge_bb);
                // Return a no-op instruction for the match arm.
                // The last instruction in merge_bb will be whatever follows.
                return Ok(None);
            }
            lir::Inst::Return(v) => {
                // Compute the value to return, then delegate to the typed-return helper.
                let ret_val = v.codegen(ctx, srcmap)?;
                let ret_ty = ctx.curr_ret_ty.clone().expect("missing curr_ret_ty");
                ctx.build_typed_return(&ret_ty, ret_val)?
            }
            // skip all of the control instructions (expect return), which will be processed later
            lir::Inst::Goto(idx) => {
                let bb = ctx.get_block(*idx);
                ctx.builder.build_unconditional_branch(bb)?
            }
            lir::Inst::Break(b) => b.codegen(ctx, srcmap)?,
            lir::Inst::If(if_expr) => if_expr.codegen(ctx, srcmap)?,
            lir::Inst::PushTraceEntry(entry) => {
                let fn_name_global = ctx.create_cstring_global(&entry.fn_name, "trace.fn");
                let file_global = ctx.create_cstring_global(&entry.file, "trace.file");
                let i32_ty = ctx.lcx.i32_type();
                let line_val = i32_ty.const_int(entry.line as u64, false);
                let col_val = i32_ty.const_int(entry.col as u64, false);
                ctx.push_trace_entry(
                    fn_name_global.as_pointer_value(),
                    file_global.as_pointer_value(),
                    line_val,
                    col_val,
                )?;
                return Ok(None);
            }
        }))
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Value {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        match self {
            lir::Value::VarRef(_) => {
                unreachable!("COMPILER BUG: this should be removed by this point")
            }
            lir::Value::Empty => Ok(ctx.unit()),
            lir::Value::Uninit(ty) => {
                if ty.is_unit() || ty.is_never() {
                    Ok(ctx.unit())
                } else {
                    Ok(ctx.to_llvm_type(ty).const_zero())
                }
            }
            lir::Value::Atom(a) => a.codegen(ctx, srcmap),
            lir::Value::Malloc(m) => m.codegen(ctx, srcmap),
            lir::Value::Call(c) => Ok(match c.codegen(ctx, srcmap)? {
                LoweredCall::Value(v) => v,
                LoweredCall::Call { call, ret_slot } => ret_slot
                    .map(|p| p.as_basic_value_enum())
                    .unwrap_or_else(|| {
                        call.try_as_basic_value()
                            .basic()
                            .unwrap_or_else(|| ctx.unit())
                    }),
                LoweredCall::Inst(_) => {
                    unreachable!("instruction should not be used in place of a value")
                }
            }),
            lir::Value::CExternCall(_) => todo!("codegen lir::CExternCall: {}", self),
            lir::Value::Select(_) => todo!("codegen lir::Select: {}", self),
            lir::Value::Phi(phi) => phi.codegen(ctx, srcmap),
            lir::Value::Load(l) => l.codegen(ctx, srcmap),
            lir::Value::Extract(e) => e.codegen(ctx, srcmap),
            lir::Value::Lea(lea) => lea.codegen(ctx, srcmap),
            lir::Value::GetField(g) => g.codegen(ctx, srcmap),
            lir::Value::BasicOp(b) => b.codegen(ctx, srcmap),
            lir::Value::Cast(c) => c.codegen(ctx, srcmap),
            lir::Value::Enum(_) => {
                unreachable!(
                    "Value::Enum must only appear as SetLocal RHS; lower via build_enum_init"
                )
            }
            lir::Value::EnumTag(t) => t.codegen(ctx, srcmap),
            lir::Value::EnumField(e) => e.codegen(ctx, srcmap),
            lir::Value::Upgrade(inner) => {
                // upgrade(id *T) -> nilable[*T]: check strong_count, if > 0
                // increment it and return Some(shared_ref), else return None.
                let data_ptr = inner.codegen(ctx, srcmap)?.into_pointer_value();
                let base_ptr = ctx.get_rc_base_ptr(data_ptr)?;
                let count_ptr = ctx.get_rc_count_ptr(base_ptr, lir::RefCountKind::Strong)?;

                let count_ty = ctx.ptr_type();
                let strong_count = ctx
                    .builder
                    .build_load(count_ty, count_ptr, "rc_strong")?
                    .into_int_value();

                let is_alive = ctx.builder.build_int_compare(
                    IntPredicate::UGT,
                    strong_count,
                    count_ty.const_int(0, false),
                    "rc_alive",
                )?;

                // Nilable result: { i1, ptr }
                let bool_ty = ctx.lcx.bool_type();
                let ptr_ty = ctx.lcx.ptr_type(AddressSpace::default());
                let nilable_ty = ctx.lcx.struct_type(&[bool_ty.into(), ptr_ty.into()], false);
                let slot = ctx.builder.build_alloca(nilable_ty, "upgrade_result")?;

                let fn_val = ctx.get_fn();
                let some_bb = ctx.lcx.append_basic_block(fn_val, "upgrade_some");
                let none_bb = ctx.lcx.append_basic_block(fn_val, "upgrade_none");
                let merge_bb = ctx.lcx.append_basic_block(fn_val, "upgrade_merge");

                ctx.builder
                    .build_conditional_branch(is_alive, some_bb, none_bb)?;

                // some: increment strong_count, store { true, data_ptr }
                ctx.builder.position_at_end(some_bb);
                let new_count = ctx.builder.build_int_add(
                    strong_count,
                    count_ty.const_int(1, false),
                    "rc_inc",
                )?;
                ctx.builder.build_store(count_ptr, new_count)?;
                let is_some_ptr = ctx
                    .builder
                    .build_struct_gep(nilable_ty, slot, 0, "is_some")?;
                ctx.builder
                    .build_store(is_some_ptr, bool_ty.const_int(1, false))?;
                let payload_ptr = ctx
                    .builder
                    .build_struct_gep(nilable_ty, slot, 1, "payload")?;
                ctx.builder.build_store(payload_ptr, data_ptr)?;
                ctx.builder.build_unconditional_branch(merge_bb)?;

                // none: store { false, null }
                ctx.builder.position_at_end(none_bb);
                let is_some_ptr = ctx
                    .builder
                    .build_struct_gep(nilable_ty, slot, 0, "is_some")?;
                ctx.builder
                    .build_store(is_some_ptr, bool_ty.const_int(0, false))?;
                let payload_ptr = ctx
                    .builder
                    .build_struct_gep(nilable_ty, slot, 1, "payload")?;
                ctx.builder.build_store(payload_ptr, ptr_ty.const_null())?;
                ctx.builder.build_unconditional_branch(merge_bb)?;

                ctx.builder.position_at_end(merge_bb);
                Ok(slot.as_basic_value_enum())
            }
            lir::Value::IntConvert(_) => todo!("codegen lir::IntConvert: {}", self),
            lir::Value::Type(_) => todo!("codegen lir::Type: {}", self),
            lir::Value::Closure(closure) => {
                let handle_ty = closure.handle.ty.mono().clone();
                let llvm_struct = ctx.get_struct_type(&closure.handle.path, &[]);
                let slot = ctx.alloca(&handle_ty)?;

                let function = ctx.fn_index.get(&closure.fn_name).unwrap_or_else(|| {
                    panic!(
                        "cannot find function `{}` when lowering closure value",
                        closure.fn_name
                    )
                });
                let fn_ptr = function
                    .as_global_value()
                    .as_pointer_value()
                    .as_basic_value_enum();
                let fn_field = ctx
                    .builder
                    .build_struct_gep(llvm_struct, slot, 0, "closure.fn")?;
                ctx.builder.build_store(fn_field, fn_ptr)?;

                let env_raw = closure.env.codegen(ctx, srcmap)?;
                let env_value = ctx.maybe_load_pointer(env_raw)?;
                let env_field =
                    ctx.builder
                        .build_struct_gep(llvm_struct, slot, 1, "closure.env")?;
                ctx.builder.build_store(env_field, env_value)?;

                Ok(slot.as_basic_value_enum())
            }
        }
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Malloc {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        let orig_ty = self.ty.mono();
        let element_ty = match orig_ty.clone() {
            Ty::Ref(inner)
            | Ty::MutRef(inner)
            | Ty::IdRef(inner)
            | Ty::RawPtr(inner)
            | Ty::Borrow(inner)
            | Ty::BorrowMut(inner) => *inner,
            ty => ty,
        };

        let pointee_ty = element_ty.clone();

        let llvm_elem_ty = ctx.to_llvm_type(&element_ty);

        log::debug!(
            "[malloc] orig_ty={} pointee_ty={} elem_ray_ty={} elem_llvm_ty={} count={:?}",
            orig_ty,
            pointee_ty,
            element_ty,
            llvm_elem_ty,
            self.count,
        );

        let size = match &self.count {
            lir::Atom::Variable(v) => {
                let mut size_value = v.codegen(ctx, srcmap)?;
                while let BasicValueEnum::PointerValue(ptr) = size_value {
                    size_value = ctx.load_pointer(ptr)?;
                }
                size_value
            }
            &lir::Atom::UintConst(count, _) => {
                if count == 1 {
                    if LLVMCodegenCtx::is_refcounted_alloc(&orig_ty) {
                        // Refcounted allocation: prepend [strong_count | weak_count] header.
                        let header_size = ctx.rc_header_size()?;
                        let data_size = ctx.llvm_size_of(llvm_elem_ty, "data_size")?;
                        let total =
                            ctx.builder
                                .build_int_add(header_size, data_size, "rc_total_size")?;
                        let td = ctx.target_machine.get_target_data();
                        let align = td.get_abi_alignment(&llvm_elem_ty);
                        let align_val = ctx.ptr_type().const_int(align as u64, false);
                        let alloc_fn = ctx.get_or_declare_alloc();
                        let base = ctx
                            .builder
                            .build_call(
                                alloc_fn,
                                &[total.into(), align_val.into()],
                                &format!("rc_alloc:<*{}>", pointee_ty),
                            )?
                            .try_as_basic_value()
                            .unwrap_basic()
                            .into_pointer_value();

                        // strong_count = 1
                        ctx.builder
                            .build_store(base, ctx.ptr_type().const_int(1, false))?;

                        // weak_count = 0
                        let weak_ptr = unsafe {
                            ctx.builder.build_gep(
                                ctx.ptr_type(),
                                base,
                                &[ctx.ptr_type().const_int(1, false)],
                                "weak_count_ptr",
                            )?
                        };
                        ctx.builder
                            .build_store(weak_ptr, ctx.ptr_type().const_int(0, false))?;

                        // data_ptr = base + header_size
                        let data_ptr = unsafe {
                            ctx.builder.build_gep(
                                ctx.lcx.i8_type(),
                                base,
                                &[header_size],
                                "rc_data_ptr",
                            )?
                        };

                        ctx.register_pointee_ty(data_ptr, pointee_ty.clone());
                        return Ok(data_ptr.as_basic_value_enum());
                    }

                    // Non-refcounted allocation (rawptr, bare types).
                    let elem_size = ctx.llvm_size_of(llvm_elem_ty, "elem_size")?;
                    let td = ctx.target_machine.get_target_data();
                    let elem_align = td.get_abi_alignment(&llvm_elem_ty);
                    let elem_align_val = ctx.ptr_type().const_int(elem_align as u64, false);
                    let alloc_fn = ctx.get_or_declare_alloc();
                    let ptr = ctx
                        .builder
                        .build_call(
                            alloc_fn,
                            &[elem_size.into(), elem_align_val.into()],
                            &format!("malloc1:<*{}>", pointee_ty),
                        )?
                        .try_as_basic_value()
                        .unwrap_basic()
                        .into_pointer_value();
                    ctx.register_pointee_ty(ptr, pointee_ty.clone());
                    return Ok(ptr.as_basic_value_enum());
                }

                ctx.ptr_type().const_int(count, false).as_basic_value_enum()
            }
            lir::Atom::Size(_) => todo!(),
            lir::Atom::FuncRef(_)
            | lir::Atom::BoolConst(_)
            | lir::Atom::CharConst(_)
            | lir::Atom::IntConst(..)
            | lir::Atom::FloatConst(..)
            | lir::Atom::RawString(_)
            | lir::Atom::NilConst => panic!(
                "COMPILER BUG: invalid count expression for lir::Malloc: {}",
                self.count
            ),
        };

        let elem_size = ctx.llvm_size_of(llvm_elem_ty, "elem_size")?;
        let total_size =
            ctx.builder
                .build_int_mul(elem_size, size.into_int_value(), "array_total_size")?;
        let td = ctx.target_machine.get_target_data();
        let arr_align = td.get_abi_alignment(&llvm_elem_ty);
        let arr_align_val = ctx.ptr_type().const_int(arr_align as u64, false);
        let alloc_fn = ctx.get_or_declare_alloc();
        let ptr = ctx
            .builder
            .build_call(
                alloc_fn,
                &[total_size.into(), arr_align_val.into()],
                &format!("malloc_array:<*{}>", pointee_ty),
            )?
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value();
        ctx.register_pointee_ty(ptr, pointee_ty);
        Ok(ptr.as_basic_value_enum())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Load {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        log::debug!("[load] generating: {:?}", self);
        let mut ptr = self.src.codegen(ctx, srcmap)?.into_pointer_value();
        if ctx.is_local_slot(&ptr) {
            // since slots themselves are pointers to whatever is inside
            // we need to do an initial load of the slot first
            log::debug!("[load] loading pointer from local slot: {}", ptr);
            ptr = ctx.load_pointer(ptr)?.into_pointer_value();
            log::debug!("[load] loaded pointer from local slot: {}", ptr);
        }

        if self.offset.ptrs > 0 {
            log::debug!(
                "[load] get element pointer offset.ptrs={}",
                self.offset.ptrs
            );
            ptr = ctx.get_element_ptr(ptr, self.offset.ptrs)?;
            log::debug!("[load] loaded pointer after GEP: {}", ptr);
        }

        if self.offset.bytes > 0 {
            log::debug!(
                "[load] byte offset pointer offset.bytes={}",
                self.offset.bytes
            );
            ptr = ctx.byte_offset_ptr(ptr, self.offset.bytes)?;
            log::debug!("[load] loaded pointer after byte offset: {}", ptr);
        }

        log::debug!("[load] dereferencing: {}", ptr);
        let value = ctx.load_pointer(ptr)?;
        log::debug!("[load] derefenced ptr into: {}", value);
        Ok(value)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Extract {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        log::debug!("[extract] generating: {:?}", self);
        let mut value = self.src.codegen(ctx, srcmap)?;
        if let BasicValueEnum::PointerValue(ptr) = value {
            value = ctx.load_pointer(ptr)?;
        }
        let idx = self.index as u32;
        let extracted =
            ctx.builder
                .build_extract_value(value.into_struct_value(), idx, "extract")?;
        Ok(extracted.as_basic_value_enum())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Insert {
    type Output = Result<InstructionValue<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        log::debug!("[insert] generating: {:?}", self);
        let ptr = match self.src {
            lir::Variable::Local(idx) => ctx.get_local(idx),
            _ => self.src.codegen(ctx, srcmap)?.into_pointer_value(),
        };
        let dst_ty = ctx.get_pointee_ty(ptr).clone();
        let base = if self.index == 0 {
            let llvm_ty = ctx.to_llvm_type(&dst_ty);
            match llvm_ty {
                BasicTypeEnum::StructType(struct_ty) => {
                    struct_ty.const_zero().as_basic_value_enum()
                }
                _ => panic!("insert expects aggregate base, got {}", dst_ty),
            }
        } else {
            ctx.load_pointer(ptr)?
        };
        let mut value = self.value.codegen(ctx, srcmap)?;
        if let BasicValueEnum::PointerValue(ptr) = value {
            value = ctx.load_pointer(ptr)?;
        }
        let idx = self.index as u32;
        let inserted =
            ctx.builder
                .build_insert_value(base.into_struct_value(), value, idx, "insert")?;
        ctx.store(ptr, inserted.as_basic_value_enum())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Store {
    type Output = Result<InstructionValue<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        match self.dst {
            lir::Variable::Data(..) => todo!(),
            lir::Variable::Global(..) => todo!(),
            lir::Variable::Local(idx) => {
                let mut ptr = ctx.get_local(idx);
                // if the local holds a pointer, we are storing to the pointee
                let pointee_ty = ctx.get_pointee_ty(ptr).clone();
                if pointee_ty.is_any_pointer() {
                    ptr = ctx.load_pointer(ptr)?.into_pointer_value();
                }

                if self.offset > 0 {
                    ptr = ctx.get_element_ptr(ptr, self.offset)?;
                }

                let value = self.value.codegen(ctx, srcmap)?;
                ctx.store(ptr, value)
            }
            lir::Variable::Unit => todo!(),
        }
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Lea {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        let ptr = match &self.offset {
            lir::LeaOffset::Const(offset) => {
                // generate the base pointer
                let var = self.var.codegen(ctx, srcmap)?;
                let mut ptr = var.into_pointer_value();

                // use the offset to get the pointer
                if offset.ptrs > 0 {
                    ptr = ctx.get_element_ptr(ptr, offset.ptrs)?;
                }

                if offset.bytes > 0 {
                    ptr = ctx.byte_offset_ptr(ptr, offset.bytes)?;
                }

                ptr
            }
            lir::LeaOffset::Field(_, field) => ctx.get_field_ptr(&self.var, field)?,
        };

        Ok(ptr.as_basic_value_enum())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::If {
    type Output = Result<InstructionValue<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, _: &SourceMap) -> Self::Output {
        let val = ctx.load_local(self.cond_loc)?.into_int_value();
        let then_block = ctx.get_block(self.then_label);
        let else_block = ctx.get_block(self.else_label);
        ctx.builder
            .build_conditional_branch(val, then_block, else_block)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Phi {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, _: &SourceMap) -> Self::Output {
        let curr_block = ctx.builder.get_insert_block().unwrap();
        // find the first non-phi instruction and use that to position the phi node
        let mut inst = curr_block.get_first_instruction();
        loop {
            if let Some(i) = inst {
                if i.get_opcode() == InstructionOpcode::Phi {
                    inst = i.get_next_instruction();
                    continue;
                }
            }
            break;
        }

        if let Some(inst) = inst {
            ctx.builder.position_at(curr_block, &inst);
        }

        // TODO: is there a better way to do this?
        let values = self.values();
        let (_, first_idx) = values.first().copied().unwrap();
        let ty = ctx.get_local_llvm_ty(first_idx);

        let phi = ctx.builder.build_phi(ty, "")?;
        for &(block_idx, loc_idx) in values {
            let bb = ctx.get_block(block_idx);
            if let Some(last) = bb.get_last_instruction() {
                // position before because the last instruction is an exit
                ctx.builder.position_before(&last);
            } else {
                ctx.builder.position_at_end(bb);
            }
            let val = ctx.load_local(loc_idx)?;
            phi.add_incoming(&[(&val, bb)]);
        }

        // position the builder back at the end of the block
        ctx.builder.position_at_end(curr_block);

        Ok(phi.as_basic_value())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Break {
    type Output = Result<InstructionValue<'ctx>, BuilderError>;

    fn codegen(&self, _: &mut LLVMCodegenCtx, _: &SourceMap) -> Self::Output {
        unimplemented!("lir::Break::codegen")
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::GetField {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, _: &SourceMap) -> Self::Output {
        let ptr = ctx.get_field_ptr(&self.src, &self.field)?;

        log::debug!(
            "[GetField] src={:?} field={} ptr={} pointee_ty={}",
            self.src,
            self.field,
            ptr.to_string(),
            ctx.get_pointee_ty(ptr)
        );

        // we expect the value of the field here, so load it
        ctx.load_pointer(ptr)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::SetField {
    type Output = Result<InstructionValue<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        let ptr = ctx.get_field_ptr(&self.dst, &self.field)?;
        let field_ty = ctx.get_pointee_ty(ptr).clone();

        log::debug!(
            "[SetField] dst={:?} field={} ptr={} field_ty={}",
            self.dst,
            self.field,
            ptr.to_string(),
            field_ty
        );

        // If the field itself is an aggregate (struct/tuple/array), copy bytes via memcpy.
        let value = self.value.codegen(ctx, srcmap)?;
        if field_ty.is_aggregate() {
            log::debug!("[SetField] aggregate field; using memcpy");
            return ctx.memcpy_aggregate_from_value(ptr, &field_ty, value);
        }

        // Non-aggregate field: use regular store semantics (with pointer/value fixups).
        ctx.store(ptr, value)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Cast {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        log::debug!("[Cast::codegen] src = {}, ty = {}", self.src, self.ty);
        let mut val = self.src.codegen(ctx, srcmap)?;
        val = ctx.maybe_load_pointer(val)?;

        let ty = ctx.to_llvm_type(&self.ty);

        log::debug!("[Cast::codegen] RHS value = {}, llvm_ty = {}", val, ty);
        Ok(match (val, ty) {
            (BasicValueEnum::IntValue(int_val), BasicTypeEnum::PointerType(ptr_type)) => ctx
                .builder
                .build_int_to_ptr(int_val, ptr_type, "")?
                .as_basic_value_enum(),
            (BasicValueEnum::PointerValue(ptr_val), BasicTypeEnum::IntType(int_type)) => ctx
                .builder
                .build_ptr_to_int(ptr_val, int_type, "")?
                .as_basic_value_enum(),
            (BasicValueEnum::IntValue(int_val), _) => ctx
                .builder
                .build_int_cast(int_val, ty.into_int_type(), "")?
                .as_basic_value_enum(),
            _ => {
                let bit_cast_value = ctx.builder.build_bit_cast(val, ty, "")?;
                if let BasicValueEnum::PointerValue(ptr) = bit_cast_value {
                    if let Some(pointee_ty) = self.ty.unwrap_pointer() {
                        ctx.register_pointee_ty(ptr, pointee_ty.clone());
                    }
                }
                bit_cast_value
            }
        })
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::EnumTag {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, _: &SourceMap) -> Self::Output {
        let src_ty = ctx.type_of(&self.src).clone();
        let (path, args) = match src_ty {
            Ty::Proj(path, args) => (path, args),
            other => panic!("EnumTag: source is not a nominal enum type: {}", other),
        };
        let enum_llvm_ty = ctx.get_enum_llvm_type(&path, &args);
        let src_ptr = match &self.src {
            lir::Variable::Local(idx) => ctx.get_local(*idx),
            other => panic!("EnumTag: src must be a local variable: {:?}", other),
        };
        let zero = ctx.zero();
        let tag_field = ctx.ptr_type().const_int(0, false);
        let tag_ptr = unsafe {
            ctx.builder
                .build_gep(enum_llvm_ty, src_ptr, &[zero, tag_field], "enum_tag_ptr")?
        };
        ctx.register_pointee_ty(tag_ptr, Ty::i32());
        ctx.load_pointer(tag_ptr)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::EnumField {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, _: &SourceMap) -> Self::Output {
        let src_ty = ctx.type_of(&self.src).clone();
        let args = match &src_ty {
            Ty::Proj(_, args) => args.clone(),
            _ => vec![],
        };

        // Instantiate the enum definition with the type arguments.
        let mut enum_ty = ctx
            .enum_defs
            .get(&self.enum_path)
            .cloned()
            .unwrap_or_else(|| panic!("EnumField: enum not found: {}", self.enum_path));
        if !args.is_empty() {
            let vars = enum_ty.ty.vars.clone();
            let mut subst = Subst::new();
            for (var, arg) in vars.into_iter().zip(args.iter()) {
                subst.insert(var, arg.clone());
            }
            enum_ty.apply_subst(&subst);
        }

        let variant = enum_ty
            .variants
            .iter()
            .find(|v| v.tag == self.variant_tag)
            .unwrap_or_else(|| {
                panic!(
                    "EnumField: variant tag {} not found in {}",
                    self.variant_tag, self.enum_path
                )
            });

        // Compute the byte offset of the target field within the payload byte array,
        // using the same alignment calculation as build_enum_init.
        let mut byte_offset: u64 = 0;
        for field_scheme in variant.field_types.iter().take(self.field_idx) {
            let field_llvm_ty = ctx.to_llvm_type(field_scheme.mono());
            let td = ctx.target_machine.get_target_data();
            let align = td.get_preferred_alignment(&field_llvm_ty) as u64;
            let size = td.get_abi_size(&field_llvm_ty);
            byte_offset = (byte_offset + align - 1) & !(align - 1);
            byte_offset += size;
        }
        // Align for the target field itself.
        let target_field_llvm_ty = ctx.to_llvm_type(&self.field_ty);
        let td = ctx.target_machine.get_target_data();
        let target_align = td.get_preferred_alignment(&target_field_llvm_ty) as u64;
        byte_offset = (byte_offset + target_align - 1) & !(target_align - 1);

        let enum_llvm_ty = ctx.get_enum_llvm_type(&self.enum_path, &args);
        let src_ptr = match &self.src {
            lir::Variable::Local(idx) => ctx.get_local(*idx),
            other => panic!("EnumField: src must be a local variable: {:?}", other),
        };

        // GEP to the payload byte array (struct field 1).
        let zero = ctx.zero();
        let payload_field = ctx.ptr_type().const_int(1, false);
        let payload_ptr = unsafe {
            ctx.builder.build_gep(
                enum_llvm_ty,
                src_ptr,
                &[zero, payload_field],
                "enum_payload_ptr",
            )?
        };

        // GEP to the field's byte offset within the payload.
        let field_ptr = if byte_offset == 0 {
            payload_ptr
        } else {
            let off_val = ctx.ptr_type().const_int(byte_offset, false);
            unsafe {
                ctx.builder.build_gep(
                    ctx.lcx.i8_type(),
                    payload_ptr,
                    &[off_val],
                    "enum_field_ptr",
                )?
            }
        };
        ctx.register_pointee_ty(field_ptr, self.field_ty.clone());
        ctx.load_pointer(field_ptr)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Call {
    type Output = Result<LoweredCall<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        if let Some(&kind) = ctx.intrinsics.get(&self.fn_name) {
            return self.codegen_intrinsic(kind, ctx, srcmap);
        }

        // Look up callee to inspect its Ray function type for parameter and
        // return information (used for sret decisions and, later, for
        // argument marshaling).
        let callee_mono = self.callee_ty.mono();
        let (ray_param_tys, ret_ty) = callee_mono.try_borrow_fn().unwrap_or_else(|_| {
            panic!(
                "type for callee is not a function: {} ({})",
                self.fn_name, self.callee_ty
            )
        });

        if let Some(fn_idx) = self.fn_ref {
            let func_ptr = ctx.load_local(fn_idx)?.into_pointer_value();
            let (call, ret_slot) =
                ctx.build_indirect_call(func_ptr, &self.args, ray_param_tys, ret_ty, srcmap)?;
            return Ok(LoweredCall::Call { call, ret_slot });
        }

        // Marshal arguments using the same rule as Inst::Call.
        let Some(&function) = ctx.fn_index.get(&self.fn_name) else {
            panic!(
                "cannot find function `{}` in index for value-call\navailable functions are:\n{}",
                self.fn_name,
                map_join(&ctx.fn_index, "\n", |(path, func)| format!(
                    "  {}: {}",
                    path, func
                ))
            )
        };
        let fn_ty = function.get_type();
        let expected_params = fn_ty.get_param_types();

        if ret_ty.is_aggregate() {
            let (call, ret_slot) = ctx.build_sret_call(
                function,
                &self.args,
                &expected_params,
                ray_param_tys,
                ret_ty,
                srcmap,
            )?;
            return Ok(LoweredCall::Call {
                call,
                ret_slot: Some(ret_slot),
            });
        }

        // Non-aggregate: regular call and unwrap pointer args as needed.
        let call = ctx.build_call(
            function,
            &self.args,
            &expected_params,
            ray_param_tys,
            srcmap,
        )?;
        Ok(LoweredCall::Call {
            call,
            ret_slot: None,
        })
    }
}

impl<'a, 'ctx> CallCodegenExt<'a, 'ctx> for lir::Call {
    fn codegen_intrinsic(
        &self,
        kind: lir::IntrinsicKind,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
    ) -> Result<LoweredCall<'ctx>, BuilderError> {
        match kind {
            lir::IntrinsicKind::PtrAdd => self.codegen_ptr_offset(ctx, srcmap, true),
            lir::IntrinsicKind::PtrSub => self.codegen_ptr_offset(ctx, srcmap, false),
            lir::IntrinsicKind::DerefRef
            | lir::IntrinsicKind::DerefRaw
            | lir::IntrinsicKind::DerefBorrow => self.codegen_deref(ctx, srcmap),
            lir::IntrinsicKind::SizeOf => self.codegen_sizeof(ctx),
            lir::IntrinsicKind::Memcopy => {
                let dst = self.args.get(0).expect("memcopy expects dest argument");
                let src = self.args.get(1).expect("memcopy expects src argument");
                let size_atom =
                    lir::Atom::Variable(self.args.get(2).expect("memcopy expects size").clone());
                let inst = ctx.build_memcpy(dst, src, &size_atom, srcmap)?;
                Ok(LoweredCall::Inst(inst))
            }
            lir::IntrinsicKind::Alloc => {
                // alloc(type['a], count: uint) -> rawptr['a]
                // Compute sizeof(T), multiply by count, call __wasi_alloc.
                let meta_ty = ctx.type_of(&self.args[0]).clone();
                let elem_ty = meta_ty.type_argument_at(0).unwrap_or(&Ty::Never).clone();
                let llvm_elem_ty = ctx.to_llvm_type(&elem_ty);
                let elem_size = ctx.llvm_size_of(llvm_elem_ty, "elem_size")?;

                let count_val = self.eval_intrinsic_int(ctx, srcmap, 1)?;
                let count_cast =
                    ctx.builder
                        .build_int_cast(count_val, ctx.ptr_type(), "alloc_count")?;
                let total_size =
                    ctx.builder
                        .build_int_mul(elem_size, count_cast, "alloc_total_size")?;

                let td = ctx.target_machine.get_target_data();
                let align = td.get_abi_alignment(&llvm_elem_ty);
                let align_val = ctx.ptr_type().const_int(align as u64, false);

                let alloc_fn = ctx.get_or_declare_alloc();
                let ptr = ctx
                    .builder
                    .build_call(
                        alloc_fn,
                        &[total_size.into(), align_val.into()],
                        "alloc_raw",
                    )?
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value();
                ctx.register_pointee_ty(ptr, elem_ty);
                Ok(LoweredCall::Value(ptr.as_basic_value_enum()))
            }
            lir::IntrinsicKind::IntHashBytes => {
                // Returns `(u64, uint)` where:
                // - the `u64` is the value's low bytes packed little-endian
                // - the `uint` is the byte length of the input integer type
                let val = self.eval_intrinsic_int(ctx, srcmap, 0)?;
                let bit_width = val.get_type().get_bit_width();
                if bit_width == 0 {
                    panic!("int_hash_bytes: zero-width integer");
                }
                if bit_width > 64 {
                    panic!(
                        "int_hash_bytes: integers wider than 64 bits are not supported (got {})",
                        bit_width
                    );
                }

                let byte_len = ((bit_width + 7) / 8) as u64;
                let i64_ty = ctx.lcx.i64_type();
                let casted = ctx.builder.build_int_cast(val, i64_ty, "")?;
                let packed = if bit_width < 64 {
                    let mask_u128 = (1u128 << bit_width) - 1;
                    let mask = i64_ty.const_int(mask_u128 as u64, false);
                    ctx.builder.build_and(casted, mask, "")?
                } else {
                    casted
                };

                let len = ctx.ptr_type().const_int(byte_len, false);
                let tuple_ty = ctx
                    .lcx
                    .struct_type(&[i64_ty.as_basic_type_enum(), ctx.ptr_type().into()], false);
                let with_packed = ctx.builder.build_insert_value(
                    tuple_ty.const_zero(),
                    packed.as_basic_value_enum(),
                    0,
                    "",
                )?;
                let with_len = ctx.builder.build_insert_value(with_packed, len, 1, "")?;
                Ok(LoweredCall::Value(with_len.as_basic_value_enum()))
            }
            lir::IntrinsicKind::BoolEq
            | lir::IntrinsicKind::IntEq
            | lir::IntrinsicKind::I8Eq
            | lir::IntrinsicKind::I16Eq
            | lir::IntrinsicKind::I32Eq
            | lir::IntrinsicKind::I64Eq
            | lir::IntrinsicKind::UintEq
            | lir::IntrinsicKind::U8Eq
            | lir::IntrinsicKind::U16Eq
            | lir::IntrinsicKind::U32Eq
            | lir::IntrinsicKind::U64Eq => {
                self.codegen_basic_op(lir::Op::Eq, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::BoolNeq
            | lir::IntrinsicKind::IntNeq
            | lir::IntrinsicKind::I8Neq
            | lir::IntrinsicKind::I16Neq
            | lir::IntrinsicKind::I32Neq
            | lir::IntrinsicKind::I64Neq
            | lir::IntrinsicKind::UintNeq
            | lir::IntrinsicKind::U8Neq
            | lir::IntrinsicKind::U16Neq
            | lir::IntrinsicKind::U32Neq
            | lir::IntrinsicKind::U64Neq => {
                self.codegen_basic_op(lir::Op::Neq, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntAdd
            | lir::IntrinsicKind::I8Add
            | lir::IntrinsicKind::I16Add
            | lir::IntrinsicKind::I32Add
            | lir::IntrinsicKind::I64Add
            | lir::IntrinsicKind::UintAdd
            | lir::IntrinsicKind::U8Add
            | lir::IntrinsicKind::U16Add
            | lir::IntrinsicKind::U32Add
            | lir::IntrinsicKind::U64Add => {
                self.codegen_basic_op(lir::Op::Add, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntSub
            | lir::IntrinsicKind::I8Sub
            | lir::IntrinsicKind::I16Sub
            | lir::IntrinsicKind::I32Sub
            | lir::IntrinsicKind::I64Sub
            | lir::IntrinsicKind::UintSub
            | lir::IntrinsicKind::U8Sub
            | lir::IntrinsicKind::U16Sub
            | lir::IntrinsicKind::U32Sub
            | lir::IntrinsicKind::U64Sub => {
                self.codegen_basic_op(lir::Op::Sub, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntMul
            | lir::IntrinsicKind::I8Mul
            | lir::IntrinsicKind::I16Mul
            | lir::IntrinsicKind::I32Mul
            | lir::IntrinsicKind::I64Mul
            | lir::IntrinsicKind::UintMul
            | lir::IntrinsicKind::U8Mul
            | lir::IntrinsicKind::U16Mul
            | lir::IntrinsicKind::U32Mul
            | lir::IntrinsicKind::U64Mul => {
                self.codegen_basic_op(lir::Op::Mul, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntDiv
            | lir::IntrinsicKind::I8Div
            | lir::IntrinsicKind::I16Div
            | lir::IntrinsicKind::I32Div
            | lir::IntrinsicKind::I64Div
            | lir::IntrinsicKind::UintDiv
            | lir::IntrinsicKind::U8Div
            | lir::IntrinsicKind::U16Div
            | lir::IntrinsicKind::U32Div
            | lir::IntrinsicKind::U64Div => {
                self.codegen_basic_op(lir::Op::Div, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntMod
            | lir::IntrinsicKind::I8Mod
            | lir::IntrinsicKind::I16Mod
            | lir::IntrinsicKind::I32Mod
            | lir::IntrinsicKind::I64Mod
            | lir::IntrinsicKind::UintMod
            | lir::IntrinsicKind::U8Mod
            | lir::IntrinsicKind::U16Mod
            | lir::IntrinsicKind::U32Mod
            | lir::IntrinsicKind::U64Mod => {
                self.codegen_basic_op(lir::Op::Mod, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntNeg
            | lir::IntrinsicKind::I8Neg
            | lir::IntrinsicKind::I16Neg
            | lir::IntrinsicKind::I32Neg
            | lir::IntrinsicKind::I64Neg => self.codegen_basic_op(lir::Op::Neg, true, ctx, srcmap),
            lir::IntrinsicKind::IntBitAnd
            | lir::IntrinsicKind::I8BitAnd
            | lir::IntrinsicKind::I16BitAnd
            | lir::IntrinsicKind::I32BitAnd
            | lir::IntrinsicKind::I64BitAnd
            | lir::IntrinsicKind::UintBitAnd
            | lir::IntrinsicKind::U8BitAnd
            | lir::IntrinsicKind::U16BitAnd
            | lir::IntrinsicKind::U32BitAnd
            | lir::IntrinsicKind::U64BitAnd => {
                self.codegen_basic_op(lir::Op::BitAnd, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntBitOr
            | lir::IntrinsicKind::I8BitOr
            | lir::IntrinsicKind::I16BitOr
            | lir::IntrinsicKind::I32BitOr
            | lir::IntrinsicKind::I64BitOr
            | lir::IntrinsicKind::UintBitOr
            | lir::IntrinsicKind::U8BitOr
            | lir::IntrinsicKind::U16BitOr
            | lir::IntrinsicKind::U32BitOr
            | lir::IntrinsicKind::U64BitOr => {
                self.codegen_basic_op(lir::Op::BitOr, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntBitXor
            | lir::IntrinsicKind::I8BitXor
            | lir::IntrinsicKind::I16BitXor
            | lir::IntrinsicKind::I32BitXor
            | lir::IntrinsicKind::I64BitXor
            | lir::IntrinsicKind::UintBitXor
            | lir::IntrinsicKind::U8BitXor
            | lir::IntrinsicKind::U16BitXor
            | lir::IntrinsicKind::U32BitXor
            | lir::IntrinsicKind::U64BitXor => {
                self.codegen_basic_op(lir::Op::BitXor, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntLt
            | lir::IntrinsicKind::I8Lt
            | lir::IntrinsicKind::I16Lt
            | lir::IntrinsicKind::I32Lt
            | lir::IntrinsicKind::I64Lt
            | lir::IntrinsicKind::UintLt
            | lir::IntrinsicKind::U8Lt
            | lir::IntrinsicKind::U16Lt
            | lir::IntrinsicKind::U32Lt
            | lir::IntrinsicKind::U64Lt => {
                self.codegen_basic_op(lir::Op::Lt, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntGt
            | lir::IntrinsicKind::I8Gt
            | lir::IntrinsicKind::I16Gt
            | lir::IntrinsicKind::I32Gt
            | lir::IntrinsicKind::I64Gt
            | lir::IntrinsicKind::UintGt
            | lir::IntrinsicKind::U8Gt
            | lir::IntrinsicKind::U16Gt
            | lir::IntrinsicKind::U32Gt
            | lir::IntrinsicKind::U64Gt => {
                self.codegen_basic_op(lir::Op::Gt, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntLteq
            | lir::IntrinsicKind::I8Lteq
            | lir::IntrinsicKind::I16Lteq
            | lir::IntrinsicKind::I32Lteq
            | lir::IntrinsicKind::I64Lteq
            | lir::IntrinsicKind::UintLteq
            | lir::IntrinsicKind::U8Lteq
            | lir::IntrinsicKind::U16Lteq
            | lir::IntrinsicKind::U32Lteq
            | lir::IntrinsicKind::U64Lteq => {
                self.codegen_basic_op(lir::Op::LtEq, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntGteq
            | lir::IntrinsicKind::I8Gteq
            | lir::IntrinsicKind::I16Gteq
            | lir::IntrinsicKind::I32Gteq
            | lir::IntrinsicKind::I64Gteq
            | lir::IntrinsicKind::UintGteq
            | lir::IntrinsicKind::U8Gteq
            | lir::IntrinsicKind::U16Gteq
            | lir::IntrinsicKind::U32Gteq
            | lir::IntrinsicKind::U64Gteq => {
                self.codegen_basic_op(lir::Op::GtEq, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntShl
            | lir::IntrinsicKind::I8Shl
            | lir::IntrinsicKind::I16Shl
            | lir::IntrinsicKind::I32Shl
            | lir::IntrinsicKind::I64Shl
            | lir::IntrinsicKind::UintShl
            | lir::IntrinsicKind::U8Shl
            | lir::IntrinsicKind::U16Shl
            | lir::IntrinsicKind::U32Shl
            | lir::IntrinsicKind::U64Shl => {
                self.codegen_basic_op(lir::Op::ArithShiftLeft, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntShr
            | lir::IntrinsicKind::I8Shr
            | lir::IntrinsicKind::I16Shr
            | lir::IntrinsicKind::I32Shr
            | lir::IntrinsicKind::I64Shr
            | lir::IntrinsicKind::UintShr
            | lir::IntrinsicKind::U8Shr
            | lir::IntrinsicKind::U16Shr
            | lir::IntrinsicKind::U32Shr
            | lir::IntrinsicKind::U64Shr => {
                self.codegen_basic_op(lir::Op::ArithShiftRight, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntRotl
            | lir::IntrinsicKind::I8Rotl
            | lir::IntrinsicKind::I16Rotl
            | lir::IntrinsicKind::I32Rotl
            | lir::IntrinsicKind::I64Rotl
            | lir::IntrinsicKind::UintRotl
            | lir::IntrinsicKind::U8Rotl
            | lir::IntrinsicKind::U16Rotl
            | lir::IntrinsicKind::U32Rotl
            | lir::IntrinsicKind::U64Rotl => {
                self.codegen_basic_op(lir::Op::RotateLeft, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::IntRotr
            | lir::IntrinsicKind::I8Rotr
            | lir::IntrinsicKind::I16Rotr
            | lir::IntrinsicKind::I32Rotr
            | lir::IntrinsicKind::I64Rotr
            | lir::IntrinsicKind::UintRotr
            | lir::IntrinsicKind::U8Rotr
            | lir::IntrinsicKind::U16Rotr
            | lir::IntrinsicKind::U32Rotr
            | lir::IntrinsicKind::U64Rotr => {
                self.codegen_basic_op(lir::Op::RotateRight, kind.is_signed(), ctx, srcmap)
            }
            lir::IntrinsicKind::BoolAnd => self.codegen_basic_op(lir::Op::And, false, ctx, srcmap),
            lir::IntrinsicKind::BoolOr => self.codegen_basic_op(lir::Op::Or, false, ctx, srcmap),
            lir::IntrinsicKind::BoolNot => self.codegen_basic_op(lir::Op::Not, false, ctx, srcmap),
            lir::IntrinsicKind::Panic => {
                // arg 0 = msg: string
                let msg_val = self.args[0].codegen(ctx, srcmap)?;
                let msg = ctx.maybe_load_pointer(msg_val)?;
                // 1. store true → context.unwinding
                ctx.store_unwinding_flag(ctx.lcx.bool_type().const_int(1, false))?;
                // 2. store msg → context.panic_message
                ctx.store_panic_message(msg)?;
                // 3. store 0 → context.trace_count
                let ctx_ptr = ctx.get_thread_ctx_ptr();
                let ctx_ty = ctx.thread_context_type();
                let trace_ptr =
                    ctx.builder
                        .build_struct_gep(ctx_ty, ctx_ptr, 2, "trace_count_ptr")?;
                ctx.builder
                    .build_store(trace_ptr, ctx.lcx.i32_type().const_zero())?;
                Ok(LoweredCall::Value(ctx.unit()))
            }
            lir::IntrinsicKind::PanicIsUnwinding => {
                let flag = ctx.load_unwinding_flag()?;
                Ok(LoweredCall::Value(flag.into()))
            }
            lir::IntrinsicKind::PanicClearUnwinding => {
                ctx.store_unwinding_flag(ctx.lcx.bool_type().const_int(0, false))?;
                Ok(LoweredCall::Value(ctx.unit()))
            }
            lir::IntrinsicKind::PanicLoadMessage => {
                let msg = ctx.load_panic_message()?;
                Ok(LoweredCall::Value(msg))
            }
            lir::IntrinsicKind::PanicPrintTrace => {
                ctx.print_trace()?;
                Ok(LoweredCall::Value(ctx.unit()))
            }
        }
    }

    fn codegen_ptr_offset(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
        is_add: bool,
    ) -> Result<LoweredCall<'ctx>, BuilderError> {
        let ptr_val = self.eval_intrinsic_ptr(ctx, srcmap, 0)?;
        let offset_val = self.eval_intrinsic_int(ctx, srcmap, 1)?;
        log::debug!(
            "[codegen_ptr_offset] ptr_val={:?} offset_val={:?} pointee_ty={}",
            ptr_val,
            offset_val,
            ctx.get_pointee_ty(ptr_val)
        );
        let pointee_ty = ctx.get_pointee_ty(ptr_val).clone();
        let llvm_pointee_ty = ctx.to_llvm_type(&pointee_ty);
        let elem_size = ctx.llvm_size_of(llvm_pointee_ty, "elem_size")?;
        log::debug!("[codegen_ptr_offset] elem_size={}", elem_size);

        let ptr_int = ctx
            .builder
            .build_ptr_to_int(ptr_val, ctx.ptr_type(), "ptr_as_int")?;
        let offset_cast = ctx
            .builder
            .build_int_cast(offset_val, ctx.ptr_type(), "ptr_offset")?;
        let scaled_offset =
            ctx.builder
                .build_int_mul(offset_cast, elem_size, "ptr_offset_scaled")?;

        let combined = if is_add {
            ctx.builder
                .build_int_add(ptr_int, scaled_offset, "ptr_add")?
        } else {
            ctx.builder
                .build_int_sub(ptr_int, scaled_offset, "ptr_sub")?
        };

        let result_ptr =
            ctx.builder
                .build_int_to_ptr(combined, ptr_val.get_type(), "ptr_result")?;

        Ok(LoweredCall::Value(result_ptr.as_basic_value_enum()))
    }

    fn codegen_deref(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
    ) -> Result<LoweredCall<'ctx>, BuilderError> {
        let ptr_val = self.eval_intrinsic_ptr(ctx, srcmap, 0)?;
        let loaded = ctx.load_pointer(ptr_val)?;
        Ok(LoweredCall::Value(loaded))
    }

    fn codegen_sizeof(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
    ) -> Result<LoweredCall<'ctx>, BuilderError> {
        // One meta-type argument; compute size as ptr-width uint (matches Ray `uint`).
        let meta_ty = ctx.type_of(&self.args[0]).clone();
        let underlying_ty = meta_ty.type_argument_at(0).unwrap_or(&Ty::Never);
        let ll = ctx.to_llvm_type(underlying_ty);
        let size = ctx.llvm_size_of(ll, "sizeof")?;
        Ok(LoweredCall::Value(size.as_basic_value_enum()))
    }

    fn codegen_basic_op(
        &self,
        op: lir::Op,
        signed: bool,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
    ) -> Result<LoweredCall<'ctx>, BuilderError> {
        // convert the lir op and size into a wasm op
        let operands = self
            .args
            .codegen(ctx, srcmap)
            .into_iter()
            .map(|result| {
                // unwrap any pointers
                let op = result?;
                ctx.maybe_load_pointer(op)
            })
            .collect::<Result<Vec<_>, BuilderError>>()?;

        let value = match (op, signed) {
            (lir::Op::Eq, _) => ctx.builder.build_int_compare(
                IntPredicate::EQ,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Neq, _) => ctx.builder.build_int_compare(
                IntPredicate::NE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Add, _) => ctx.builder.build_int_add(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Sub, _) => ctx.builder.build_int_sub(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Mul, _) => ctx.builder.build_int_mul(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Div, true) => ctx.builder.build_int_signed_div(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Div, false) => ctx.builder.build_int_unsigned_div(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Mod, true) => ctx.builder.build_int_signed_rem(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Mod, false) => ctx.builder.build_int_unsigned_rem(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Neg, true) => ctx.builder.build_int_neg(operands[0].into_int_value(), ""),
            (lir::Op::Lt, true) => ctx.builder.build_int_compare(
                IntPredicate::SLT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Lt, false) => ctx.builder.build_int_compare(
                IntPredicate::ULT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Gt, true) => ctx.builder.build_int_compare(
                IntPredicate::SGT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Gt, false) => ctx.builder.build_int_compare(
                IntPredicate::UGT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::LtEq, true) => ctx.builder.build_int_compare(
                IntPredicate::SLE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::LtEq, false) => ctx.builder.build_int_compare(
                IntPredicate::ULE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::GtEq, true) => ctx.builder.build_int_compare(
                IntPredicate::SGE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::GtEq, false) => ctx.builder.build_int_compare(
                IntPredicate::UGE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::BitAnd, _) | (lir::Op::And, _) => ctx.builder.build_and(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::BitOr, _) | (lir::Op::Or, _) => ctx.builder.build_or(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::BitXor, _) => ctx.builder.build_xor(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Not, _) => ctx.builder.build_not(operands[0].into_int_value(), ""),
            _ => todo!("basic op: (op={}, signed={})", op, signed),
        }?
        .as_basic_value_enum();

        Ok(LoweredCall::Value(value))
    }

    fn eval_intrinsic_ptr(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
        idx: usize,
    ) -> Result<PointerValue<'ctx>, BuilderError> {
        let mut val = self.args[idx].codegen(ctx, srcmap)?;
        if let BasicValueEnum::PointerValue(ptr) = val {
            let is_slot = ctx.is_local_slot(&ptr);
            log::debug!(
                "[eval_intrinsic_ptr] arg_idx={} raw_ptr={:?} is_local_slot={}",
                idx,
                ptr,
                is_slot
            );
            if is_slot {
                val = ctx.load_pointer(ptr)?;
            }
        }

        match val {
            BasicValueEnum::PointerValue(p) => Ok(p),
            _ => panic!("intrinsic pointer operand was not a pointer"),
        }
    }

    fn eval_intrinsic_int(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        srcmap: &SourceMap,
        idx: usize,
    ) -> Result<IntValue<'ctx>, BuilderError> {
        let val = self.args[idx].codegen(ctx, srcmap)?;
        let loaded = ctx.maybe_load_pointer(val)?;
        match loaded {
            BasicValueEnum::IntValue(int) => Ok(int),
            _ => panic!("intrinsic integer operand was not an integer"),
        }
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::BasicOp {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        // convert the lir op and size into a wasm op
        let operands = self
            .operands
            .codegen(ctx, srcmap)
            .into_iter()
            .map(|result| {
                // unwrap any pointers
                let op = result?;
                ctx.maybe_load_pointer(op)
            })
            .collect::<Result<Vec<_>, BuilderError>>()?;

        Ok(match (self.op, self.signed) {
            (lir::Op::Eq, _) => ctx.builder.build_int_compare(
                IntPredicate::EQ,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Neq, _) => ctx.builder.build_int_compare(
                IntPredicate::NE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Add, _) => ctx.builder.build_int_add(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Sub, _) => ctx.builder.build_int_sub(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Mul, _) => ctx.builder.build_int_mul(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Div, true) => ctx.builder.build_int_signed_div(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Div, false) => ctx.builder.build_int_unsigned_div(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Mod, true) => ctx.builder.build_int_signed_rem(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Mod, false) => ctx.builder.build_int_unsigned_rem(
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Neg, true) => ctx.builder.build_int_neg(operands[0].into_int_value(), ""),
            (lir::Op::Lt, true) => ctx.builder.build_int_compare(
                IntPredicate::SLT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Lt, false) => ctx.builder.build_int_compare(
                IntPredicate::ULT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Gt, true) => ctx.builder.build_int_compare(
                IntPredicate::SGT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::Gt, false) => ctx.builder.build_int_compare(
                IntPredicate::UGT,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::LtEq, true) => ctx.builder.build_int_compare(
                IntPredicate::SLE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::LtEq, false) => ctx.builder.build_int_compare(
                IntPredicate::ULE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::GtEq, true) => ctx.builder.build_int_compare(
                IntPredicate::SGE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            (lir::Op::GtEq, false) => ctx.builder.build_int_compare(
                IntPredicate::UGE,
                operands[0].into_int_value(),
                operands[1].into_int_value(),
                "",
            ),
            _ => todo!("binop: ({}, {}, {})", self.op, self.size, self.signed),
        }?
        .as_basic_value_enum())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Atom {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, srcmap: &SourceMap) -> Self::Output {
        Ok(match self {
            lir::Atom::Variable(v) => v.codegen(ctx, srcmap)?,
            lir::Atom::FuncRef(func_ref) => {
                let fn_val = ctx
                    .fn_index
                    .get(&func_ref.path)
                    .unwrap_or_else(|| panic!("missing function `{}` for FuncRef", func_ref.path));
                fn_val
                    .as_global_value()
                    .as_pointer_value()
                    .as_basic_value_enum()
            }
            lir::Atom::Size(size) => ctx.size_to_int(size).as_basic_value_enum(),
            lir::Atom::CharConst(ch) => ctx
                .lcx
                .i32_type()
                .const_int(*ch as u64, false)
                .as_basic_value_enum(),
            lir::Atom::BoolConst(b) => ctx
                .lcx
                .bool_type()
                .const_int(if *b { 1 } else { 0 }, false)
                .as_basic_value_enum(),
            lir::Atom::UintConst(c, size) => ctx
                .size_to_type(size)
                .const_int(*c, false)
                .as_basic_value_enum(),
            lir::Atom::IntConst(c, size) => ctx
                .size_to_type(size)
                .const_int(*c as u64, true)
                .as_basic_value_enum(),
            lir::Atom::FloatConst(_, _) => todo!("codegen lir::Atom: {}", self),
            lir::Atom::RawString(_) => todo!("codegen lir::Atom: {}", self),
            lir::Atom::NilConst => ctx.ptr_type().const_zero().as_basic_value_enum(),
        })
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Variable {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, 'ctx>, _: &SourceMap) -> Self::Output {
        Ok(match self {
            lir::Variable::Data(path, idx) => ctx
                .data_addrs
                .get(&(path.clone(), *idx))
                .unwrap()
                .as_pointer_value()
                .as_basic_value_enum(),
            lir::Variable::Global(path, idx) => ctx
                .globals
                .get(&(path.clone(), *idx))
                .unwrap()
                .as_pointer_value()
                .as_basic_value_enum(),
            lir::Variable::Local(idx) => ctx.get_local(*idx).as_basic_value_enum(),
            lir::Variable::Unit => ctx.unit(),
        })
    }
}
