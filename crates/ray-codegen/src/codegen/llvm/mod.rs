mod attr;

use std::{
    collections::{HashMap, hash_map::Entry},
    env::{self, temp_dir},
    fs,
    io::Write,
    ops::Deref,
    ptr,
};

use inkwell::{
    self as llvm, attributes::Attribute, builder::BuilderError, passes::PassBuilderOptions,
    types::BasicMetadataTypeEnum, values::BasicMetadataValueEnum,
};
use llvm::{
    AddressSpace, IntPredicate,
    attributes::AttributeLoc,
    basic_block::BasicBlock,
    module::Linkage,
    targets::{FileType, InitializationConfig, Target as LLVMTarget, TargetMachine, TargetTriple},
    types::{BasicType, BasicTypeEnum, IntType, StructType},
    values::{
        BasicValue, BasicValueEnum, CallSiteValue, FunctionValue, GlobalValue, InstructionOpcode,
        InstructionValue, IntValue, PointerValue,
    },
};
use rand::RngCore;
use ray_core::{
    ast::{Modifier, Node},
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
    target::Target,
};
use ray_lir::{self as lir, SymbolSet};
use ray_shared::{
    optlevel::OptLevel,
    pathlib::{FilePath, ItemPath, Path},
    ty::{Ty, TyVar},
    utils::map_join,
};
use ray_typing::types::{StructTy, Subst, Substitutable};

use crate::codegen::{CodegenOptions, collect_symbols};

use super::Codegen;

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

static MALLOC_BUF: &'static [u8] = include_bytes!("../../../../../lib/libc/wasi_malloc.wasm");

lazy_static! {
    static ref MALLOC_BUF_HASH: u64 = xxhash_rust::xxh3::xxh3_64(MALLOC_BUF);
}

pub fn codegen<'a, P>(
    program: &lir::Program,
    srcmap: &SourceMap,
    lcx: &'a llvm::context::Context,
    target: &Target,
    output_path: P,
    options: CodegenOptions,
) -> Result<(), Vec<RayError>>
where
    P: FnOnce(&'static str) -> FilePath,
{
    let name = program.module_path.to_string();
    let module = lcx.create_module(&name);
    let builder = lcx.create_builder();
    let mut ctx = LLVMCodegenCtx::new(target, lcx, &module, &builder, &program.struct_types);
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

    let malloc_path = tmp_dir.clone() / format!("wasi_malloc.{}.a", *MALLOC_BUF_HASH);
    if !malloc_path.exists() {
        let mut f = fs::File::create(&malloc_path).unwrap();
        f.write_all(MALLOC_BUF).unwrap();
    }

    let wasm_path = output_path("wasm");
    log::info!("writing to {}", wasm_path);
    let curr_dir = env::current_dir().unwrap();
    if let Some(msg) = lld::link(
        target.to_string(),
        &[
            obj_path.to_string(),
            malloc_path.to_string(),
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
    let mut ctx = LLVMCodegenCtx::new(target, &context, &module, &builder, &program.struct_types);
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
enum LoweredCall<'ctx> {
    Call {
        call: CallSiteValue<'ctx>,
        ret_slot: Option<PointerValue<'ctx>>,
    },
    Value(BasicValueEnum<'ctx>),
    Inst(InstructionValue<'ctx>),
}

struct LLVMCodegenCtx<'a, 'ctx> {
    lcx: &'ctx llvm::context::Context,
    module: &'a llvm::module::Module<'ctx>,
    builder: &'a llvm::builder::Builder<'ctx>,
    target_machine: TargetMachine,
    curr_fn: Option<FunctionValue<'ctx>>,
    curr_ret_ty: Option<Ty>,
    fn_index: HashMap<Path, FunctionValue<'ctx>>,
    /// LLVM struct type cache - maps ray types to LLVM struct types.
    struct_types: HashMap<Ty, StructType<'ctx>>,
    data_addrs: HashMap<(Path, usize), GlobalValue<'ctx>>,
    globals: HashMap<(Path, usize), GlobalValue<'ctx>>,
    locals: HashMap<usize, PointerValue<'ctx>>,
    local_tys: Vec<Ty>,
    blocks: HashMap<usize, BasicBlock<'ctx>>,
    pointee_tys: HashMap<PointerValue<'ctx>, Ty>,
    sret_param: Option<PointerValue<'ctx>>,
    intrinsics: HashMap<Path, lir::IntrinsicKind>,
    /// Struct definitions from the program (both workspace and synthetic).
    struct_defs: &'a HashMap<ItemPath, StructTy>,
}

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    fn new(
        target: &Target,
        lcx: &'ctx llvm::context::Context,
        module: &'a llvm::module::Module<'ctx>,
        builder: &'a llvm::builder::Builder<'ctx>,
        struct_defs: &'a HashMap<ItemPath, StructTy>,
    ) -> Self {
        LLVMTarget::initialize_webassembly(&InitializationConfig::default());

        // create the LLVM target machine from the target parameter
        let llvm_target = LLVMTarget::from_name("wasm32").expect("could not get wasm32 target");
        let target_triple = TargetTriple::create(target.as_str());

        let target_machine = llvm_target
            .create_target_machine(
                &target_triple,
                "generic",
                "+bulk-memory",
                llvm::OptimizationLevel::Default,
                llvm::targets::RelocMode::Default,
                llvm::targets::CodeModel::Default,
            )
            .expect(&format!(
                "could not create `{}` target machine",
                llvm_target.get_name().to_str().unwrap()
            ));

        let target_data = target_machine.get_target_data();
        let data_layout = target_data.get_data_layout();
        module.set_data_layout(&data_layout);

        Self {
            lcx,
            module,
            builder,
            target_machine,
            curr_fn: None,
            curr_ret_ty: None,
            fn_index: HashMap::new(),
            struct_types: HashMap::new(),
            data_addrs: HashMap::new(),
            globals: HashMap::new(),
            locals: HashMap::new(),
            local_tys: vec![],
            blocks: HashMap::new(),
            pointee_tys: HashMap::new(),
            sret_param: None,
            intrinsics: HashMap::new(),
            struct_defs,
        }
    }

    fn ensure_wasi_globals(&mut self) {
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

    fn type_of(&self, var: &lir::Variable) -> &Ty {
        match var {
            lir::Variable::Unit => panic!("unit is untyped"),
            lir::Variable::Data(..) => panic!("data is untyped"),
            lir::Variable::Global(_, idx) => {
                todo!("type of global: {}", idx)
            }
            lir::Variable::Local(idx) => &self.local_tys[*idx],
        }
    }

    fn ptr_type(&self) -> IntType<'ctx> {
        let target_data = self.target_machine.get_target_data();
        self.lcx.ptr_sized_int_type(&target_data, None)
    }

    fn unit_type(&self) -> StructType<'ctx> {
        self.lcx.struct_type(&[], false)
    }

    fn zero(&self) -> IntValue<'ctx> {
        self.ptr_type().const_zero()
    }

    fn unit(&self) -> BasicValueEnum<'ctx> {
        self.unit_type()
            .const_named_struct(&[])
            .as_basic_value_enum()
    }

    fn size_to_int(&self, s: &lir::Size) -> IntValue<'ctx> {
        let ptr_type = self.ptr_type();
        ptr_type
            .size_of()
            .const_mul(ptr_type.const_int(s.ptrs as u64, false))
            .const_add(ptr_type.const_int(s.bytes as u64, false))
    }

    fn size_to_type(&self, s: &lir::Size) -> IntType<'ctx> {
        match s {
            lir::Size { bytes: 0, ptrs: 1 } | lir::Size { bytes: 0, ptrs: 0 } => self.ptr_type(),
            lir::Size { bytes: 8, ptrs: 0 } => self.lcx.i64_type(),
            lir::Size { bytes: 4, ptrs: 0 } => self.lcx.i32_type(),
            lir::Size { bytes: 2, ptrs: 0 } => self.lcx.i16_type(),
            lir::Size { bytes: 1, ptrs: 0 } => self.lcx.i8_type(),
            _ => panic!("cannot create int type of size: {}", s),
        }
    }

    fn get_pointee_ty(&self, ptr: PointerValue<'ctx>) -> &Ty {
        self.pointee_tys.get(&ptr).unwrap()
    }

    fn register_pointee_ty(&mut self, ptr: PointerValue<'ctx>, ty: Ty) {
        log::debug!("[register_pointee_ty] ptr={} ty={}", ptr.to_string(), ty);
        self.pointee_tys.insert(ptr, ty);
    }

    fn lookup_struct_ty(&self, path: &ItemPath) -> &StructTy {
        self.struct_defs
            .get(path)
            .expect(&format!("could not find struct type: {}", path))
    }

    fn lookup_struct_ty_instantiated(&self, def_path: &ItemPath, args: &[Ty]) -> StructTy {
        let mut struct_ty = self
            .struct_defs
            .get(def_path)
            .cloned()
            .expect(&format!("could not find struct type: {}", def_path));

        if args.is_empty() {
            return struct_ty;
        }

        let vars: Vec<TyVar> = struct_ty.ty.vars.clone();
        if vars.len() != args.len() {
            panic!(
                "cannot instantiate struct type: path={} vars={} args={}",
                def_path,
                vars.len(),
                args.len()
            );
        }

        let mut subst = Subst::new();
        for (var, arg) in vars.into_iter().zip(args.iter()) {
            subst.insert(var, arg.clone());
        }
        struct_ty.apply_subst(&subst);
        struct_ty
    }

    fn is_struct(&self, ty: &Ty) -> bool {
        if let Some(path) = ty.item_path() {
            self.struct_defs.contains_key(path)
        } else {
            false
        }
    }

    fn get_element_ty(&self, container_ty: &Ty, index: usize) -> Ty {
        match container_ty {
            Ty::Array(elem_ty, _) => elem_ty.as_ref().clone(),
            Ty::Ref(inner_ty) => inner_ty.as_ref().clone(),
            Ty::RawPtr(inner_ty) => inner_ty.as_ref().clone(),
            Ty::Proj(fqn, args) => {
                let struct_ty = self.lookup_struct_ty_instantiated(fqn, args);
                struct_ty.field_tys()[index].mono().clone()
            }
            Ty::Const(fqn) => {
                let struct_ty = self.lookup_struct_ty_instantiated(fqn, &[]);
                struct_ty.field_tys()[index].mono().clone()
            }
            ty => panic!("get_element_ty: unexpected type {}", ty),
        }
    }

    fn get_fn(&self) -> FunctionValue<'ctx> {
        self.curr_fn.unwrap()
    }

    fn get_block(&mut self, idx: usize) -> BasicBlock<'ctx> {
        let fn_val = self.get_fn();
        if !self.blocks.contains_key(&idx) {
            let bb = self.lcx.append_basic_block(fn_val, &format!("B{}", idx));
            self.blocks.insert(idx, bb);
        }

        *self.blocks.get(&idx).unwrap()
    }

    fn get_local(&self, idx: usize) -> PointerValue<'ctx> {
        *self
            .locals
            .get(&idx)
            .expect(&format!("could not find variable: {}", idx))
    }

    fn load_local(&mut self, idx: usize) -> Result<BasicValueEnum<'ctx>, BuilderError> {
        let ptr = self.get_local(idx);
        self.load_pointer(ptr)
    }

    fn is_local_slot(&mut self, ptr: &PointerValue<'ctx>) -> bool {
        self.locals.values().any(|slot_ptr| ptr == slot_ptr)
    }

    fn load_pointer(
        &mut self,
        ptr: PointerValue<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, BuilderError> {
        let pointee_ty = self.get_pointee_ty(ptr).clone();
        let llvm_ty = self.to_llvm_type(&pointee_ty);
        let loaded = self
            .builder
            .build_load(llvm_ty, ptr, &format!("load:<{}>", pointee_ty))?;
        if let Some(inner) = pointee_ty.unwrap_pointer() {
            if let BasicValueEnum::PointerValue(new_ptr) = loaded {
                self.register_pointee_ty(new_ptr, inner.clone());
            }
        }

        log::debug!(
            "[load_pointer] returning loaded value loaded={:?} from ptr={}",
            loaded,
            ptr
        );
        Ok(loaded)
    }

    fn get_element_ptr(
        &mut self,
        ptr: PointerValue<'ctx>,
        index: usize,
    ) -> Result<PointerValue<'ctx>, BuilderError> {
        log::debug!(
            "[get_element_ptr] entered with ptr={} index={}",
            ptr.to_string(),
            index
        );
        let mut container_ty = self.get_pointee_ty(ptr).clone();
        // Debug log: original pointee type and if base is a local slot
        let original_pointee = self.get_pointee_ty(ptr).clone();
        log::debug!(
            "[get_element_ptr] original_pointee_ty={} (local_slot={}) index={}",
            original_pointee,
            self.is_local_slot(&ptr),
            index
        );
        let mut base_ptr = ptr;
        log::debug!(
            "[get_element_ptr] container_ty={:?} base_ptr={:?} index={}",
            container_ty,
            base_ptr,
            index
        );
        while let Some(inner_ty) = container_ty.unwrap_pointer() {
            if !self.is_struct(inner_ty) {
                log::debug!(
                    "[get_element_ptr] breaking before load: inner_ty is not struct (inner_ty={})",
                    inner_ty
                );
                break;
            }

            container_ty = inner_ty.clone();
            log::debug!(
                "[get_element_ptr] loading base_ptr to reach struct payload: inner_ty={}",
                container_ty
            );
            base_ptr = self.load_pointer(base_ptr)?.into_pointer_value();
            log::debug!(
                "[get_element_ptr] loaded pointer: container_ty={:?} base_ptr={:?}",
                container_ty,
                base_ptr,
            );
        }

        log::debug!(
            "[get_element_ptr] after_chase: base_ptr={} container_ty={} (local_slot={})",
            base_ptr.to_string(),
            container_ty,
            self.is_local_slot(&base_ptr)
        );

        let offset = self.ptr_type().const_int(index as u64, false);

        // Build the GEP and determine the correct pointee mapping for the resulting pointer.
        let (gep, gep_pointee_ty) = if self.is_struct(&container_ty) {
            // Struct field access: compute the field Ray type and GEP into the aggregate.
            let field_ray_ty = self.get_element_ty(&container_ty, index);
            log::debug!("[get_element_ptr] field_ray_ty={:?}", field_ray_ty);

            let field_storage_llty = self.to_llvm_type(&field_ray_ty);
            log::debug!(
                "[get_element_ptr] field_storage_llvm_ty={}",
                field_storage_llty.print_to_string().to_string()
            );

            let llvm_struct = match &container_ty {
                Ty::Proj(fqn, args) => self.get_struct_type(fqn, args),
                Ty::Const(fqn) => self.get_struct_type(fqn, &[]),
                _ => panic!(
                    "get_element_ptr: expected struct type, got {}",
                    container_ty
                ),
            };
            let fqn_display = container_ty
                .item_path()
                .map(|p| p.to_string())
                .unwrap_or_default();
            log::debug!(
                "[get_element_ptr] struct GEP: fqn={} base_ptr={} offset={} llvm_struct_ty={}",
                fqn_display,
                base_ptr.to_string(),
                index,
                llvm_struct.print_to_string().to_string()
            );

            let gep = unsafe {
                self.builder
                    .build_gep(llvm_struct, base_ptr, &[self.zero(), offset], "")?
            };
            (gep, field_ray_ty)
        } else if matches!(container_ty, Ty::Array(_, _) | Ty::Ref(_) | Ty::RawPtr(_)) {
            // Array / pointer stepping: use the element type derived from the container.
            let field_ray_ty = self.get_element_ty(&container_ty, index);
            log::debug!("[get_element_ptr] field_ray_ty={:?}", field_ray_ty);

            let field_storage_llty = self.to_llvm_type(&field_ray_ty);
            log::debug!(
                "[get_element_ptr] field_storage_llvm_ty={}",
                field_storage_llty.print_to_string().to_string()
            );

            log::debug!(
                "[get_element_ptr] array/ptr GEP: base_ptr={} index={} element_ray_ty={} element_llvm_ty={}",
                base_ptr.to_string(),
                index,
                field_ray_ty,
                field_storage_llty.print_to_string().to_string()
            );

            let gep = unsafe {
                self.builder
                    .build_gep(field_storage_llty, base_ptr, &[offset], "")?
            };
            log::debug!(
                "[get_element_ptr] array/ptr pointee mapping: tracked_pointee={}",
                field_ray_ty
            );
            (gep, field_ray_ty)
        } else {
            // Fallback: treat the pointee type as the element type directly. This covers
            // heap pointers from `malloc(T, n)` where we only track the element type `T`
            // (e.g., `int`, `nilable[int]`) rather than an explicit array container.
            let element_ty = container_ty.clone();
            let element_llty = self.to_llvm_type(&element_ty);
            log::debug!(
                "[get_element_ptr] flat-element GEP: base_ptr={} index={} element_ray_ty={} element_llvm_ty={}",
                base_ptr.to_string(),
                index,
                element_ty,
                element_llty.print_to_string().to_string()
            );

            let gep = unsafe {
                self.builder
                    .build_gep(element_llty, base_ptr, &[offset], "")?
            };
            (gep, element_ty)
        };

        log::debug!(
            "[get_element_ptr] registering pointee: gep_ptr={} pointee_ty={}",
            gep.to_string(),
            gep_pointee_ty
        );
        self.register_pointee_ty(gep, gep_pointee_ty);
        log::debug!(
            "[get_element_ptr] done: returning gep_ptr={} for index={} (final_container_ty={})",
            gep.to_string(),
            index,
            container_ty
        );
        Ok(gep)
    }

    fn byte_offset_ptr(
        &mut self,
        ptr: PointerValue<'ctx>,
        bytes: usize,
    ) -> Result<PointerValue<'ctx>, BuilderError> {
        if bytes == 0 {
            return Ok(ptr);
        }

        let offset = self.ptr_type().const_int(bytes as u64, false);
        let gep = unsafe {
            self.builder
                .build_gep(self.lcx.i8_type(), ptr, &[offset], "")?
        };
        self.register_pointee_ty(gep, Ty::i8());
        Ok(gep)
    }

    fn get_local_llvm_ty(&mut self, idx: usize) -> BasicTypeEnum<'ctx> {
        let ptr = self.get_local(idx);
        let ty = self.get_pointee_ty(ptr).clone();
        self.to_llvm_type(&ty)
    }

    fn get_field_ptr(
        &mut self,
        var: &lir::Variable,
        field: &String,
    ) -> Result<PointerValue<'ctx>, BuilderError> {
        // Determine the logical LHS type, unwrapping one pointer layer for
        // cases like `*Struct` so we can inspect the underlying aggregate.
        let mut lhs_ty = self.type_of(var).clone();
        if let Some(inner) = lhs_ty.unwrap_pointer() {
            lhs_ty = inner.clone();
        }

        // Special-case `nilable['a]`, which is not a nominal struct
        // but is lowered to an Option-like aggregate:
        //   { is_some: bool, payload: 'a }
        //
        // We compute field indices and types directly from this layout
        if let Some(payload_ty) = lhs_ty.nilable_payload() {
            let (field_index, field_ty) = match field.as_str() {
                "is_some" => (0, Ty::bool()),
                "payload" => (1, payload_ty.clone()),
                _ => panic!("cannot find field {} on nilable", field),
            };

            let base_ptr = match var {
                lir::Variable::Local(idx) => self.get_local(*idx),
                lir::Variable::Data(..) | lir::Variable::Global(..) | lir::Variable::Unit => {
                    todo!("GetField for nilable from non-local variable: {:?}", var)
                }
            };

            // The local for `nilable['a]` is allocated with `to_llvm_type(lhs_ty)`,
            // which we know lowers to a literal struct `{ i1, T }`. With opaque
            // pointers we cannot query the element type from `base_ptr`, so we
            // reconstruct the struct type from the Ray type instead.
            let llvm_ty = self.to_llvm_type(&lhs_ty);
            let llvm_struct = match llvm_ty {
                BasicTypeEnum::StructType(st) => st,
                other => panic!(
                    "expected struct type for nilable, got {:?} for lhs_ty={}",
                    other, lhs_ty
                ),
            };

            let zero = self.zero();
            let field_idx = self.ptr_type().const_int(field_index as u64, false);
            let gep = unsafe {
                self.builder
                    .build_gep(llvm_struct, base_ptr, &[zero, field_idx], "")?
            };
            self.register_pointee_ty(gep, field_ty);
            return Ok(gep);
        }

        // Nominal struct case
        let lhs_fqn = lhs_ty
            .item_path()
            .expect("expected nominal type for field access");
        let lhs_ty = self.lookup_struct_ty(lhs_fqn);
        let mut offset = 0;
        let mut found = false;
        for (name, _) in lhs_ty.fields.iter() {
            if name == field {
                found = true;
                break;
            }
            offset += 1;
        }

        if !found {
            panic!("cannot find field {} on {}", field, lhs_fqn);
        }

        match var {
            lir::Variable::Data(..) => todo!(),
            lir::Variable::Global(..) => todo!(),
            lir::Variable::Local(idx) => {
                let ptr = self.get_local(*idx);
                self.get_element_ptr(ptr, offset)
            }
            lir::Variable::Unit => todo!(),
        }
    }

    fn to_llvm_type(&mut self, ty: &Ty) -> BasicTypeEnum<'ctx> {
        match ty {
            Ty::Never => todo!("to_llvm_ty: {}", ty),
            Ty::Any => todo!("to_llvm_ty: {}", ty),
            Ty::Var(_) => todo!("to_llvm_ty: {}", ty),
            Ty::Array(elem_ty, size) => self
                .to_llvm_type(elem_ty)
                .array_type(*size as u32)
                .as_basic_type_enum(),
            Ty::Tuple(tys) => self
                .lcx
                .struct_type(
                    tys.iter()
                        .map(|ty| self.to_llvm_type(ty))
                        .collect::<Vec<_>>()
                        .as_slice(),
                    false,
                )
                .into(),
            Ty::Func(_, _) | Ty::Ref(_) | Ty::RawPtr(_) => self
                .lcx
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
            Ty::Proj(fqn, args) => {
                // `nilable['a]` is represented as an Option-like aggregate:
                // `{ i1 is_some, T payload }`, where `T` is the LLVM type for `'a`.
                if let Some(name) = fqn.item_name() {
                    if name == "nilable" {
                        let payload_ty = args
                            .get(0)
                            .map(|t| self.to_llvm_type(t))
                            // Fallback to `i8` payload for ill-formed cases; this
                            // should not happen for well-typed programs.
                            .unwrap_or_else(|| self.lcx.i8_type().into());

                        return self
                            .lcx
                            .struct_type(&[self.lcx.bool_type().into(), payload_ty], false)
                            .into();
                    }
                }

                // For all other projections, lower to the underlying type.
                self.get_struct_type(fqn, args).as_basic_type_enum()
            }
            Ty::Const(fqn) => match fqn.as_str() {
                "bool" => self.lcx.bool_type().into(),
                "i8" | "u8" => self.lcx.i8_type().into(),
                "i16" | "u16" => self.lcx.i16_type().into(),
                "i32" | "u32" | "char" => self.lcx.i32_type().into(),
                "u64" | "i64" => self.lcx.i64_type().into(),
                "int" | "uint" => self.ptr_type().into(),
                _ => self.get_struct_type(fqn, &[]).as_basic_type_enum(),
            },
        }
    }

    fn to_llvm_fn_ty(
        &mut self,
        param_tys: &Vec<Ty>,
        ret_ty: &Ty,
    ) -> llvm::types::FunctionType<'ctx> {
        // If returning an aggregate, lower as sret: return void and prepend a retptr parameter.
        if ret_ty.is_aggregate() {
            let mut ll_params: Vec<BasicTypeEnum<'ctx>> = Vec::with_capacity(param_tys.len() + 1);
            // retptr is a pointer to the return aggregate type
            let retptr_ty = self
                .lcx
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum();
            ll_params.push(retptr_ty);
            for ty in param_tys.iter() {
                ll_params.push(self.to_llvm_type(ty));
            }
            return self.lcx.void_type().fn_type(
                &ll_params.into_iter().map(|t| t.into()).collect::<Vec<_>>(),
                false,
            );
        }

        // Non-aggregate returns: normal signature
        let param_tys = param_tys
            .iter()
            .map(|ty| self.to_llvm_type(ty).into())
            .collect::<Vec<_>>();
        if ret_ty.is_unit() {
            return self.lcx.void_type().fn_type(&param_tys, false);
        }

        let ret_ty = self.to_llvm_type(ret_ty);
        ret_ty.fn_type(&param_tys, false)
    }

    fn alloca(&mut self, ty: &Ty) -> Result<PointerValue<'ctx>, BuilderError> {
        let entry = self.get_fn().get_first_basic_block().unwrap();

        // get the current insert block
        let saved_bb = self.builder.get_insert_block();

        // find the _last_ alloca instruction
        let mut inst = entry.get_first_instruction();
        loop {
            if let Some(i) = inst {
                if i.get_opcode() == InstructionOpcode::Alloca {
                    inst = i.get_next_instruction();
                    continue;
                }
            }
            break;
        }

        match inst {
            Some(inst) => self.builder.position_before(&inst),
            None => self.builder.position_at_end(entry),
        }

        let llvm_ty = self.to_llvm_type(ty);

        let alloca = self
            .builder
            .build_alloca(llvm_ty, &format!("alloca:<{}>", ty))?;
        self.register_pointee_ty(alloca, ty.clone());

        // restore the position
        if let Some(bb) = saved_bb {
            self.builder.position_at_end(bb);
        }

        Ok(alloca)
    }

    fn maybe_load_pointer(
        &mut self,
        val: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, BuilderError> {
        if let BasicValueEnum::PointerValue(ptr) = val {
            self.load_pointer(ptr)
        } else {
            Ok(val)
        }
    }

    /// Marshal a single argument value to match the callee's LLVM parameter type.
    ///
    /// This uses the Ray parameter type to distinguish between:
    /// - pointer parameters: the logical argument is a pointer *value* (Ty::Ref | Ty::RawPtr),
    /// - by-value parameters lowered as addresses: the logical argument is a value,
    ///   but we pass an address to it when LLVM expects a pointer.
    fn marshal_arg_value(
        &mut self,
        ray_param_ty: &Ty,
        expected: &BasicMetadataTypeEnum<'ctx>,
        mut val: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, BuilderError> {
        let expected_is_ptr = expected.is_pointer_type();

        if expected_is_ptr {
            // Callee expects an address in LLVM IR.
            if let BasicValueEnum::PointerValue(p) = val {
                match ray_param_ty {
                    // Pointer parameter: the logical argument is a pointer value (*T | rawptr[T]).
                    // If that pointer is stored in a local slot (slot-of-pointer),
                    // load once so we pass the pointer value instead of the slot address.
                    Ty::Ref(_) | Ty::RawPtr(_) => {
                        if self.is_local_slot(&p) && self.get_pointee_ty(p).is_any_pointer() {
                            val = self.load_pointer(p)?;
                        }
                        return Ok(val);
                    }

                    // Non-pointer parameter: the logical argument is a value of type `ray_param_ty`.
                    // When LLVM expects a pointer, we pass the address of that value. For locals,
                    // the pointee type of the slot should match `ray_param_ty`.
                    _ => {
                        if self.is_local_slot(&p) {
                            let slot_ty = self.get_pointee_ty(p);
                            if slot_ty != ray_param_ty {
                                panic!(
                                    "COMPILER BUG: pointer parameter slot type mismatch; slot_ty={} ray_param_ty={} llvm_param_ty={}",
                                    slot_ty,
                                    ray_param_ty,
                                    expected.print_to_string().to_string()
                                );
                            }
                        }
                        return Ok(val);
                    }
                }
            }

            // Non-pointer value for a pointer-typed LLVM parameter should not occur
            // under correct LIR invariants; surface a clear compiler bug if it does.
            panic!(
                "COMPILER BUG: non-pointer argument for pointer parameter; ray_param_ty={} llvm_param_ty={}",
                ray_param_ty,
                expected.print_to_string().to_string()
            );
        }

        // Non-pointer LLVM parameter: unwrap any address into a value.
        //
        // If the Ray parameter type is Ty::Ref(_), then to_llvm_type(ray_param_ty)
        // should have produced a pointer-typed LLVM parameter; reaching this branch
        // would indicate an inconsistency between Ray and LLVM signatures.
        if matches!(ray_param_ty, Ty::Ref(_)) {
            panic!(
                "COMPILER BUG: Ray pointer parameter lowered to non-pointer LLVM parameter; ray_param_ty={} llvm_param_ty={}",
                ray_param_ty,
                expected.print_to_string().to_string()
            );
        }

        self.maybe_load_pointer(val)
    }

    fn store(
        &mut self,
        ptr: PointerValue<'ctx>,
        mut value: BasicValueEnum<'ctx>,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        // Decide how to treat the RHS based on what the destination slot expects.
        // 1) If destination is an aggregate (struct/tuple/array), copy bytes via memcpy.
        //    If RHS is not a pointer, spill it to a stack temp first so we can memcpy.
        // 2) Otherwise fall back to pointer/scalar-aware store semantics.
        let dest_ty = self.get_pointee_ty(ptr).clone();
        log::debug!("[store] dest_ty = {}", dest_ty);

        if dest_ty.is_aggregate() {
            // If RHS is already a pointer to an aggregate, memcpy directly.
            if let BasicValueEnum::PointerValue(rhs_ptr) = value {
                let src_ty = self.get_pointee_ty(rhs_ptr).clone();
                log::debug!("[store] value is pointer: src_ty = {}", src_ty);
                if src_ty.is_aggregate() {
                    let td = self.target_machine.get_target_data();
                    let dst_llty = self.to_llvm_type(&dest_ty);
                    let size = dst_llty.size_of().unwrap();
                    let dst_align = td.get_abi_alignment(&dst_llty);

                    let src_llty = self.to_llvm_type(&src_ty);
                    let src_align = td.get_abi_alignment(&src_llty);

                    log::debug!(
                        "[store] is_aggregate=true building memcpy: ptr={} dst_align={} rhs_ptr={}, src_align={} size={}",
                        ptr,
                        dst_align,
                        rhs_ptr,
                        src_align,
                        size
                    );
                    return Ok(self
                        .builder
                        .build_memcpy(ptr, dst_align, rhs_ptr, src_align, size)
                        .unwrap()
                        .as_instruction_value()
                        .unwrap());
                }
            }

            // Spill non-pointer (value) aggregates to a stack temp, then memcpy.
            let tmp = self.alloca(&dest_ty)?;
            // tmp points to dest_ty; remember its pointee
            self.register_pointee_ty(tmp, dest_ty.clone());

            // Store the value into the temp. For pointer RHS that's not an aggregate pointee,
            // ensure we load to a value first.
            let spilled_val = match value {
                BasicValueEnum::PointerValue(p) => self.load_pointer(p)?,
                v => v,
            };
            self.builder.build_store(tmp, spilled_val)?;

            let td = self.target_machine.get_target_data();
            let dst_llty = self.to_llvm_type(&dest_ty);
            let size = dst_llty.size_of().unwrap();
            let dst_align = td.get_abi_alignment(&dst_llty);
            let src_align = dst_align; // same type we just spilled

            log::debug!(
                "[store] building memcpy ptr={} dst_align={} tmp={} src_align={} size={}",
                ptr,
                dst_align,
                tmp,
                src_align,
                size
            );

            return Ok(self
                .builder
                .build_memcpy(ptr, dst_align, tmp, src_align, size)
                .unwrap()
                .as_instruction_value()
                .unwrap());
        }

        log::debug!(
            "[store] dest_ptr={} dest_ty={} value_kind={:?}",
            ptr.to_string(),
            dest_ty,
            value
        );
        log::debug!("[store] initial RHS kind={:?}", value);

        // Non-aggregate destinations:
        if let BasicValueEnum::PointerValue(rhs_ptr) = value
            && self.is_local_slot(&rhs_ptr)
        {
            match dest_ty {
                Ty::Ref(_) | Ty::RawPtr(_) => {
                    if let Some(rhs_pointee) = self.pointee_tys.get(&rhs_ptr) {
                        if rhs_pointee.is_any_pointer() {
                            log::debug!(
                                "[store] loading pointer RHS {} -> {:?}",
                                rhs_ptr.to_string(),
                                rhs_pointee
                            );
                            // Storing to a pointer slot, but RHS points at another pointer.
                            // Load once so we store the pointer VALUE, not the address of that pointer.
                            value = self.load_pointer(rhs_ptr)?;
                            log::debug!(
                                "[store] post-load value kind={:?} (from rhs_ptr={})",
                                value,
                                rhs_ptr.to_string()
                            );
                        }
                    }
                }
                _ => {
                    log::debug!(
                        "[store] dest scalar, loading pointer RHS {}",
                        rhs_ptr.to_string()
                    );
                    // Destination expects a non-pointer (scalar) value.
                    value = self.load_pointer(rhs_ptr)?;
                    log::debug!(
                        "[store] post-load value kind={:?} (from rhs_ptr={})",
                        value,
                        rhs_ptr.to_string()
                    );
                }
            }
        }

        let iv = self.builder.build_store(ptr, value)?;
        log::debug!(
            "[store] completed store: dest_ptr={} value_kind={:?}",
            ptr.to_string(),
            value
        );
        Ok(iv)
    }

    /// Builds set local for local index
    fn build_set_local(
        &mut self,
        idx: usize,
        value: &lir::Value,
        srcmap: &SourceMap,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        let dst_ptr = self.get_local(idx);
        let dst_ty = self.get_pointee_ty(dst_ptr).clone();

        // If destination is an aggregate (struct/tuple/array), copy bytes via memcpy
        // instead of performing an aggregate load+store.
        if dst_ty.is_aggregate() {
            let src_val = value.codegen(self, srcmap)?;
            return self.memcpy_aggregate_from_value(dst_ptr, &dst_ty, src_val);
        }

        // Non-aggregate destination: perform the normal store.
        let value = value.codegen(self, srcmap)?;
        self.store(dst_ptr, value)
    }

    /// Builds memcpy for destination, source, and size
    fn build_memcpy(
        &mut self,
        dest_var: &lir::Variable,
        src_var: &lir::Variable,
        size: &lir::Atom,
        srcmap: &SourceMap,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        let mut dest = dest_var.codegen(self, srcmap)?.into_pointer_value();
        if dest_var.is_local() && self.get_pointee_ty(dest).is_any_pointer() {
            dest = self.load_pointer(dest)?.into_pointer_value();
        }

        let mut src = src_var.codegen(self, srcmap)?.into_pointer_value();
        if src_var.is_local() && self.get_pointee_ty(src).is_any_pointer() {
            src = self.load_pointer(src)?.into_pointer_value();
        }
        let size_val = size.codegen(self, srcmap)?;
        let size = self.maybe_load_pointer(size_val)?.into_int_value();
        let td = self.target_machine.get_target_data();
        let dest_align = {
            let dest_pointee = self.get_pointee_ty(dest).clone();
            let dest_llvm_ty = self.to_llvm_type(&dest_pointee);
            td.get_abi_alignment(&dest_llvm_ty)
        };
        let src_align = {
            let src_pointee = self.get_pointee_ty(src).clone();
            let src_llvm_ty = self.to_llvm_type(&src_pointee);
            td.get_abi_alignment(&src_llvm_ty)
        };
        Ok(self
            .builder
            .build_memcpy(dest, dest_align, src, src_align, size)
            .unwrap()
            .as_instruction_value()
            .unwrap())
    }

    /// Copy an aggregate (struct/tuple/array) into `dst_ptr` from a source value that
    /// is expected to be an address (or address-of-address) of a compatible aggregate.
    /// Falls back to a regular store if the value is not a pointer.
    fn memcpy_aggregate_from_value(
        &mut self,
        dst_ptr: PointerValue<'ctx>,
        dst_ty: &Ty,
        src_val: BasicValueEnum<'ctx>,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        log::debug!(
            "[memcpy_aggregate_from_value] entered: dst_ptr={} dst_ty={:?}",
            dst_ptr.to_string(),
            dst_ty
        );
        // Resolve a source pointer to the aggregate storage.
        let src_ptr = if let BasicValueEnum::PointerValue(p) = src_val {
            if self.get_pointee_ty(p).is_any_pointer() {
                // If it's a pointer-to-pointer, load once to try to reach aggregate storage.
                self.load_pointer(p)?.into_pointer_value()
            } else {
                p
            }
        } else {
            // Not a pointer; let the generic store handle it (scalar/pointer cases).
            return self.store(dst_ptr, src_val);
        };

        // Compute size and ABI alignments for memcpy.
        let td = self.target_machine.get_target_data();
        let dst_llvm_ty = self.to_llvm_type(dst_ty);
        let size = dst_llvm_ty.size_of().unwrap();
        let dst_align = td.get_abi_alignment(&dst_llvm_ty);

        let src_ty = self.get_pointee_ty(src_ptr).clone();
        let src_llvm_ty = self.to_llvm_type(&src_ty);
        let src_align = td.get_abi_alignment(&src_llvm_ty);

        Ok(self
            .builder
            .build_memcpy(dst_ptr, dst_align, src_ptr, src_align, size)
            .unwrap()
            .as_instruction_value()
            .unwrap())
    }

    fn build_call_args(
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
    fn build_call(
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

    fn build_sret_call_args(
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
    fn build_sret_call(
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
    fn build_indirect_call(
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

    /// Build a return for the current function, using Ray's return type to
    /// decide whether to return a pointer (aggregate) or a scalar value.
    /// For aggregates without sret, if the LLVM return is non-pointer we load once.
    fn build_typed_return(
        &mut self,
        ret_ty: &Ty,
        ret_val: BasicValueEnum<'ctx>,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        let fn_val = self.get_fn();
        let llvm_ret_is_void = fn_val.get_type().get_return_type().is_none();
        if llvm_ret_is_void {
            // If Ray return type is aggregate, store into sret param and return void.
            if ret_ty.is_aggregate() {
                let dst_ptr = self
                    .sret_param
                    .expect("missing sret_param for aggregate return");
                self.memcpy_aggregate_from_value(dst_ptr, ret_ty, ret_val)?;
            }
            return self.builder.build_return(None);
        }

        if ret_ty.is_aggregate() {
            // Aggregate returns should be sret; interim behavior:
            // - If LLVM return type is a pointer, pass pointer as-is.
            // - Else load once to return by value.
            let llvm_ret_ty = fn_val.get_type().get_return_type().unwrap();
            match (ret_val, llvm_ret_ty) {
                (BasicValueEnum::PointerValue(p), BasicTypeEnum::PointerType(_)) => {
                    return self.builder.build_return(Some(&p.as_basic_value_enum()));
                }
                (BasicValueEnum::PointerValue(p), _) => {
                    let loaded = self.load_pointer(p)?;
                    return self.builder.build_return(Some(&loaded));
                }
                _ => {
                    // Not a pointer? Return whatever we have (shouldn't happen with our LIR invariants).
                    return self.builder.build_return(Some(&ret_val));
                }
            }
        }

        // Non-aggregate return: if it's a pointer, load once into a value.
        let fn_val = self.get_fn();
        let llvm_ret_ty = fn_val.get_type().get_return_type().unwrap();

        // If LLVM expects a pointer, return the pointer as-is; otherwise, load once,
        // but if the pointer is a slot holding a pointer (Ty::Ref(_)), load once so we
        // return the pointer value, not the address of the slot.
        match (ret_val, llvm_ret_ty) {
            (BasicValueEnum::PointerValue(p), BasicTypeEnum::PointerType(_)) => {
                // If this pointer is actually a local slot that contains a pointer value
                // (we track such slots with pointee type Ty::Ref(_) | Ty::RawPtr(_)), load once so the
                // function returns the pointer VALUE and not the address of the slot.
                if self.get_pointee_ty(p).is_any_pointer() {
                    let loaded = self.load_pointer(p)?;
                    self.builder.build_return(Some(&loaded))
                } else {
                    self.builder.build_return(Some(&p.as_basic_value_enum()))
                }
            }
            (BasicValueEnum::PointerValue(p), _) => {
                let loaded = self.load_pointer(p)?;
                self.builder.build_return(Some(&loaded))
            }
            (v, _) => self.builder.build_return(Some(&v)),
        }
    }

    fn fn_attr(&self, fn_val: FunctionValue<'ctx>, key: &str, val: &str) {
        let attribute = self.lcx.create_string_attribute(key, val);
        fn_val.add_attribute(AttributeLoc::Function, attribute);
    }

    fn get_struct_type(&mut self, path: &ItemPath, args: &[Ty]) -> StructType<'ctx> {
        let key = Ty::nominal(path.clone(), args.to_vec());

        if let Some(st) = self.struct_types.get(&key) {
            return st.clone();
        }

        let opaque = self.lcx.opaque_struct_type(&key.to_mangled());
        self.struct_types.insert(key.clone(), opaque);

        let struct_ty = self.lookup_struct_ty_instantiated(path, args);

        let field_types = struct_ty
            .fields
            .iter()
            .map(|(_, ty)| self.to_llvm_type(ty.mono()))
            .collect::<Vec<_>>();

        let llvm_struct = self
            .struct_types
            .get(&key)
            .expect("struct not registered")
            .clone();
        llvm_struct.set_body(field_types.as_slice(), false);
        llvm_struct
    }
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

        if let Some(malloc_fn) = ctx.module.get_function("malloc") {
            // use the __wasi_malloc import for malloc
            malloc_fn.as_global_value().set_name("__wasi_malloc");
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

            lir::Inst::Free(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Call(call) => {
                match call.codegen(ctx, srcmap)? {
                    LoweredCall::Value(_v) => {
                        // Intrinsic folded to a value in expression position; as a statement call,
                        // this becomes a no-op.
                        return Ok(None);
                    }
                    LoweredCall::Call { call, .. } => call
                        .try_as_basic_value()
                        .either(|val| val.as_instruction_value().unwrap(), |inst| inst),
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
            lir::Inst::IncRef(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::DecRef(_) => todo!("codegen lir::Inst: {}", self),
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
            lir::Value::Atom(a) => a.codegen(ctx, srcmap),
            lir::Value::Malloc(m) => m.codegen(ctx, srcmap),
            lir::Value::Call(c) => Ok(match c.codegen(ctx, srcmap)? {
                LoweredCall::Value(v) => v,
                LoweredCall::Call { call, ret_slot } => ret_slot
                    .map(|p| p.as_basic_value_enum())
                    .unwrap_or_else(|| call.try_as_basic_value().left_or_else(|_| ctx.unit())),
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
            Ty::Ref(inner) | Ty::RawPtr(inner) => *inner,
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
                    let ptr = ctx
                        .builder
                        .build_malloc(llvm_elem_ty, &format!("malloc1:<*{}>", pointee_ty))?;
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

        let ptr = ctx.builder.build_array_malloc(
            llvm_elem_ty,
            size.into_int_value(),
            &format!("malloc_array:<*{}>", pointee_ty),
        )?;
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
                if ctx.get_pointee_ty(ptr).is_any_pointer() {
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
            lir::IntrinsicKind::DerefRef | lir::IntrinsicKind::DerefRaw => {
                self.codegen_deref(ctx, srcmap)
            }
            lir::IntrinsicKind::SizeOf => self.codegen_sizeof(ctx),
            lir::IntrinsicKind::Memcopy => {
                let dst = self.args.get(0).expect("memcopy expects dest argument");
                let src = self.args.get(1).expect("memcopy expects src argument");
                let size_atom =
                    lir::Atom::Variable(self.args.get(2).expect("memcopy expects size").clone());
                let inst = ctx.build_memcpy(dst, src, &size_atom, srcmap)?;
                Ok(LoweredCall::Inst(inst))
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
        let elem_size_raw = ctx
            .to_llvm_type(&pointee_ty)
            .size_of()
            .expect("element size must be computable");
        log::debug!("[codegen_ptr_offset] elem_size_raw={}", elem_size_raw);
        let elem_size = ctx
            .builder
            .build_int_cast(elem_size_raw, ctx.ptr_type(), "elem_size")?;

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
        let raw = ll.size_of().expect("could not compute sizeof for type");
        let cast = ctx.builder.build_int_cast(raw, ctx.ptr_type(), "")?;
        Ok(LoweredCall::Value(cast.as_basic_value_enum()))
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
