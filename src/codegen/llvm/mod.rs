mod attr;

use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    env::{self, temp_dir},
    fs,
    io::Write,
    ops::Deref,
    ptr,
};

use inkwell::{
    self as llvm, attributes::Attribute, builder::BuilderError, passes::PassBuilderOptions,
    types::BasicMetadataTypeEnum,
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

use crate::{
    ast::{Modifier, Node, Path},
    codegen::{CodegenOptions, collect_symbols},
    driver::OptLevel,
    errors::RayError,
    lir,
    pathlib::FilePath,
    span::SourceMap,
    target::Target,
    typing::{
        TyCtx,
        ty::{NominalKind, Ty},
    },
};

use super::Codegen;

static MALLOC_BUF: &'static [u8] = include_bytes!("../../../lib/libc/wasi_malloc.wasm");

lazy_static! {
    static ref MALLOC_BUF_HASH: u64 = xxhash_rust::xxh3::xxh3_64(MALLOC_BUF);
}

pub fn codegen<'a, 'ctx, P>(
    program: &lir::Program,
    tcx: &TyCtx,
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
    let mut ctx = LLVMCodegenCtx::new(target, lcx, &module, &builder, tcx);
    if let Some(err) = program.codegen(&mut ctx, tcx, srcmap).err() {
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
    lld::link(
        target.to_string(),
        &[
            obj_path.to_string(),
            malloc_path.to_string(),
            str!("--no-entry"),
            str!("-o"),
            curr_dir.join(wasm_path).to_str().unwrap().to_string(),
        ],
    )
    .ok()
    .unwrap();
    Ok(())
}

// Represents the result of lowering a call in codegen: either a normal callsite (with optional ret slot), or a folded value.
enum LoweredCall<'ctx> {
    Call {
        call: CallSiteValue<'ctx>,
        ret_slot: Option<PointerValue<'ctx>>,
    },
    Value(BasicValueEnum<'ctx>),
}

struct LLVMCodegenCtx<'a, 'ctx> {
    lcx: &'ctx llvm::context::Context,
    module: &'a llvm::module::Module<'ctx>,
    builder: &'a llvm::builder::Builder<'ctx>,
    target_machine: TargetMachine,
    curr_fn: Option<FunctionValue<'ctx>>,
    curr_ret_ty: Option<Ty>,
    fn_index: HashMap<Path, FunctionValue<'ctx>>,
    tcx: &'a TyCtx,
    struct_types: HashMap<String, StructType<'ctx>>,
    data_addrs: HashMap<(Path, usize), GlobalValue<'ctx>>,
    globals: HashMap<(Path, usize), GlobalValue<'ctx>>,
    locals: HashMap<usize, PointerValue<'ctx>>,
    local_tys: Vec<Ty>,
    blocks: HashMap<usize, BasicBlock<'ctx>>,
    pointee_tys: HashMap<PointerValue<'ctx>, Ty>,
    sret_param: Option<PointerValue<'ctx>>,
}

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    fn new(
        target: &Target,
        lcx: &'ctx llvm::context::Context,
        module: &'a llvm::module::Module<'ctx>,
        builder: &'a llvm::builder::Builder<'ctx>,
        tcx: &'a TyCtx,
    ) -> Self {
        LLVMTarget::initialize_webassembly(&InitializationConfig::default());

        // create the LLVM target machine from the target parameter
        let llvm_target = LLVMTarget::from_name("wasm32").expect("could not get wasm32 target");
        let target_triple = TargetTriple::create(target.as_str());

        let target_machine = llvm_target
            .create_target_machine(
                &target_triple,
                "generic",
                "",
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
            tcx,
            struct_types: HashMap::new(),
            data_addrs: HashMap::new(),
            globals: HashMap::new(),
            locals: HashMap::new(),
            local_tys: vec![],
            blocks: HashMap::new(),
            pointee_tys: HashMap::new(),
            sret_param: None,
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

    fn get_element_ty(&self, container_ty: &Ty, index: usize) -> Ty {
        match container_ty {
            ty if ty.is_struct(self.tcx) || ty.is_record(self.tcx) => {
                let fqn = ty
                    .get_path()
                    .expect("struct type missing fully-qualified name");
                let struct_ty = self
                    .tcx
                    .get_struct_ty(&fqn)
                    .expect("could not find struct type");
                struct_ty.field_tys()[index].mono().clone()
            }
            Ty::Array(elem_ty, _) => elem_ty.as_ref().clone(),
            Ty::Ptr(inner_ty) => inner_ty.as_ref().clone(),
            ty => panic!("container is not indexable: {:?}", ty),
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
        *self.locals.get(&idx).expect("could not find variable")
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
        if let Ty::Ptr(inner) = &pointee_ty {
            if let BasicValueEnum::PointerValue(new_ptr) = loaded {
                self.register_pointee_ty(new_ptr, inner.as_ref().clone());
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
        while let Ty::Ptr(inner) = &container_ty {
            let inner_ty = inner.as_ref();
            if !(inner_ty.is_struct(self.tcx) || inner_ty.is_record(self.tcx)) {
                log::debug!(
                    "[get_element_ptr] breaking before load: inner_ty is not struct/record (inner_ty={})",
                    inner_ty
                );
                break;
            }

            container_ty = inner_ty.clone();
            log::debug!(
                "[get_element_ptr] loading base_ptr to reach struct/record payload: inner_ty={}",
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
        // Compute the element (field) Ray type after resolving the actual container type.
        let field_ray_ty = self.get_element_ty(&container_ty, index);
        log::debug!("[get_element_ptr] field_ray_ty={:?}", field_ray_ty);

        let field_storage_llty = self.to_llvm_type(&field_ray_ty);
        log::debug!(
            "[get_element_ptr] field_storage_llvm_ty={}",
            field_storage_llty.print_to_string().to_string()
        );

        let offset = self.ptr_type().const_int(index as u64, false);

        // Build the GEP and determine the correct pointee mapping for the resulting pointer.
        let (gep, gep_pointee_ty) = match &container_ty {
            ty if ty.is_struct(self.tcx) || ty.is_record(self.tcx) => {
                let fqn = ty
                    .get_path()
                    .expect("struct type missing fully-qualified name");
                let llvm_struct = self.get_struct_type(&fqn);
                log::debug!(
                    "[get_element_ptr] struct/record GEP: fqn={} base_ptr={} offset={} llvm_struct_ty={}",
                    fqn,
                    base_ptr.to_string(),
                    index,
                    llvm_struct.print_to_string().to_string()
                );

                // For struct fields, the *storage* type may be a pointer (e.g., when the Ray field
                // type is itself a struct and we lower structs-as-references). If the storage is a
                // pointer, the GEP points at a pointer slot, so the pointee type we track should be
                // `Ptr(field_ty)`; otherwise it is just `field_ty`.
                let gep = unsafe {
                    self.builder
                        .build_gep(llvm_struct, base_ptr, &[self.zero(), offset], "")?
                };
                let pointee = match field_storage_llty {
                    BasicTypeEnum::PointerType(_) if field_ray_ty.is_struct(self.tcx) => {
                        Ty::Ptr(Box::new(field_ray_ty.clone()))
                    }
                    _ => field_ray_ty.clone(),
                };
                (gep, pointee)
            }
            Ty::Array(_, _) | Ty::Ptr(_) => {
                log::debug!(
                    "[get_element_ptr] array/ptr GEP: base_ptr={} index={} element_ray_ty={} element_llvm_ty={}",
                    base_ptr.to_string(),
                    index,
                    field_ray_ty,
                    self.to_llvm_type(&field_ray_ty)
                        .print_to_string()
                        .to_string()
                );
                // For arrays/pointers, the element storage type is exactly `field_ray_ty`.
                let gep = unsafe {
                    self.builder.build_gep(
                        self.to_llvm_type(&field_ray_ty),
                        base_ptr,
                        &[offset],
                        "",
                    )?
                };
                log::debug!(
                    "[get_element_ptr] array/ptr pointee mapping: tracked_pointee={}",
                    field_ray_ty
                );
                (gep, field_ray_ty.clone())
            }
            ty => panic!("container is not indexable: {:?}", ty),
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
        tcx: &TyCtx,
    ) -> Result<PointerValue<'ctx>, BuilderError> {
        // get the field offset and size
        let mut lhs_ty = self.type_of(var);
        if let Ty::Ptr(inner) = lhs_ty {
            lhs_ty = &inner;
        }

        let lhs_fqn = lhs_ty.get_path().unwrap();
        let lhs_ty = tcx.get_struct_ty(&lhs_fqn).unwrap();
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
            Ty::Func(_, _) => todo!("to_llvm_ty: {}", ty),
            Ty::Accessor(_, _) => todo!("to_llvm_ty: {}", ty),
            Ty::Var(_) => todo!("to_llvm_ty: {}", ty),
            Ty::Union(_) => todo!("to_llvm_ty: {}", ty),
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
            Ty::Ptr(_) => self
                .lcx
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
            Ty::Projection(ty, ..) => self.to_llvm_type(ty),
            Ty::Const(fqn) => match fqn.as_str() {
                "bool" => self.lcx.bool_type().into(),
                "i8" | "u8" => self.lcx.i8_type().into(),
                "i16" | "u16" => self.lcx.i16_type().into(),
                "i32" | "u32" | "char" => self.lcx.i32_type().into(),
                "u64" | "i64" => self.lcx.i64_type().into(),
                "int" | "uint" => self.ptr_type().into(),
                _ => {
                    let fqn = ty.get_path().unwrap();
                    let def = self.tcx.get_struct_ty(&fqn).unwrap();
                    match def.kind {
                        NominalKind::Record => self.get_struct_type(&fqn).as_basic_type_enum(),
                        NominalKind::Struct => self
                            .lcx
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum(),
                    }
                }
            },
        }
    }

    fn to_llvm_fn_ty(
        &mut self,
        param_tys: &Vec<Ty>,
        ret_ty: &Ty,
    ) -> llvm::types::FunctionType<'ctx> {
        // If returning an aggregate, lower as sret: return void and prepend a retptr parameter.
        if ret_ty.is_aggregate() && !ret_ty.is_struct(self.tcx) {
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

        // Struct values lower to raw pointers; local slots holding a struct therefore
        // contain a pointer value
        // Track that as Ty::Ptr(struct_ty) so later loads know to unwrap once
        let pointee_ty = if ty.innermost().is_struct(self.tcx) {
            Ty::ptr(ty.clone())
        } else {
            ty.clone()
        };

        let alloca = self
            .builder
            .build_alloca(llvm_ty, &format!("alloca:<{}>", pointee_ty))?;
        self.register_pointee_ty(alloca, pointee_ty);

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

    fn store(
        &mut self,
        ptr: PointerValue<'ctx>,
        mut value: BasicValueEnum<'ctx>,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        // Decide how to treat the RHS based on what the destination slot expects.
        // 1) If destination is an aggregate (record/tuple/array), copy bytes via memcpy.
        //    If RHS is not a pointer, spill it to a stack temp first so we can memcpy.
        // 2) Otherwise fall back to pointer/scalar-aware store semantics.
        let dest_ty = self.get_pointee_ty(ptr).clone();
        log::debug!("[store] dest_ty = {}", dest_ty);

        if dest_ty.is_aggregate() && !dest_ty.is_struct(self.tcx) {
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
                Ty::Ptr(_) => {
                    if let Some(rhs_pointee) = self.pointee_tys.get(&rhs_ptr) {
                        if matches!(rhs_pointee, Ty::Ptr(_)) {
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
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        let dst_ptr = self.get_local(idx);
        let dst_ty = self.get_pointee_ty(dst_ptr).clone();

        // If destination is an aggregate (struct/tuple/array), copy bytes via memcpy
        // instead of performing an aggregate load+store.
        if dst_ty.is_aggregate() && !dst_ty.is_struct(self.tcx) {
            let src_val = value.codegen(self, tcx, srcmap)?;
            return self.memcpy_aggregate_from_value(dst_ptr, &dst_ty, src_val);
        }

        // Non-aggregate destination: perform the normal store.
        let value = value.codegen(self, tcx, srcmap)?;
        self.store(dst_ptr, value)
    }

    /// Builds memcpy for destination, source, and size
    fn build_memcpy(
        &mut self,
        dest_var: &lir::Variable,
        src_var: &lir::Variable,
        size: &lir::Atom,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        let mut dest = dest_var.codegen(self, tcx, srcmap)?.into_pointer_value();
        if dest_var.is_local() && matches!(self.get_pointee_ty(dest), Ty::Ptr(_)) {
            dest = self.load_pointer(dest)?.into_pointer_value();
        }

        let mut src = src_var.codegen(self, tcx, srcmap)?.into_pointer_value();
        if src_var.is_local() && matches!(self.get_pointee_ty(src), Ty::Ptr(_)) {
            src = self.load_pointer(src)?.into_pointer_value();
        }
        let size = size.codegen(self, tcx, srcmap)?.into_int_value();
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
            // If p already points to an aggregate, use it directly.
            if self.get_pointee_ty(p).is_aggregate() {
                p
            } else {
                // If it's a pointer-to-pointer, load once to try to reach aggregate storage.
                match self.get_pointee_ty(p) {
                    Ty::Ptr(_) => self.load_pointer(p)?.into_pointer_value(),
                    _ => p, // best-effort fallback
                }
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

    /// Build a function call
    fn build_call(
        &mut self,
        function: FunctionValue<'ctx>,
        args: &Vec<lir::Variable>,
        expected_params: &Vec<BasicMetadataTypeEnum<'ctx>>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Result<CallSiteValue<'ctx>, BuilderError> {
        let arg_vals = args.codegen(self, tcx, srcmap);
        let args = expected_params
            .into_iter()
            .zip(arg_vals.into_iter())
            .map(|(expected, result)| {
                let mut v = result?;
                if expected.is_pointer_type() {
                    // Callee expects an address. If our value is a pointer whose pointee is itself a
                    // pointer (i.e., the local slot holding a pointer), load once so we pass the
                    // pointer VALUE sitting in that slot instead of the address of the slot.
                    if let BasicValueEnum::PointerValue(p) = v {
                        if matches!(self.get_pointee_ty(p), Ty::Ptr(_)) {
                            v = self.load_pointer(p)?;
                        }
                    }
                    Ok(v.into())
                } else {
                    // Non-pointer parameter: unwrap any address into a value.
                    Ok(self.maybe_load_pointer(v)?.into())
                }
            })
            .collect::<Result<Vec<_>, BuilderError>>()?;
        self.builder.build_call(function, args.as_slice(), "")
    }

    /// Build a function call with aggregate return type
    fn build_sret_call(
        &mut self,
        function: FunctionValue<'ctx>,
        args: &Vec<lir::Variable>,
        expected_params: &Vec<BasicMetadataTypeEnum<'ctx>>,
        ret_ty: &Ty,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Result<(CallSiteValue<'ctx>, PointerValue<'ctx>), BuilderError> {
        let arg_vals = args.codegen(self, tcx, srcmap);

        // sret: allocate a local return slot, pass as first arg, and return the pointer as the value.
        let ret_slot = self.alloca(ret_ty)?;

        // prepend retptr then the rest of marshalled args
        let mut marshalled: Vec<BasicValueEnum> = Vec::with_capacity(expected_params.len());

        // First expected param must be a pointer (retptr)
        marshalled.push(ret_slot.as_basic_value_enum());

        // Zip remaining expected params with arg values
        for (expected, result) in expected_params
            .into_iter()
            .skip(1)
            .zip(arg_vals.into_iter())
        {
            let v = result?;
            if expected.is_pointer_type() {
                marshalled.push(v);
            } else {
                marshalled.push(self.maybe_load_pointer(v)?);
            }
        }

        // Emit the call (returns void in sret case)
        let call = self.builder.build_call(
            function,
            &marshalled.iter().map(|v| (*v).into()).collect::<Vec<_>>(),
            "",
        )?;

        // Return the call value and the ret_slot pointer.
        Ok((call, ret_slot))
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
            if ret_ty.is_aggregate() && !ret_ty.is_struct(self.tcx) {
                let dst_ptr = self
                    .sret_param
                    .expect("missing sret_param for aggregate return");
                self.memcpy_aggregate_from_value(dst_ptr, ret_ty, ret_val)?;
            }
            return self.builder.build_return(None);
        }

        if ret_ty.is_aggregate() && !ret_ty.is_struct(self.tcx) {
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
        // but if the pointer is a slot holding a pointer (Ty::Ptr(_)), load once so we
        // return the pointer value, not the address of the slot.
        match (ret_val, llvm_ret_ty) {
            (BasicValueEnum::PointerValue(p), BasicTypeEnum::PointerType(_)) => {
                // If this pointer is actually a local slot that contains a pointer value
                // (we track such slots with pointee type Ty::Ptr(_)), load once so the
                // function returns the pointer VALUE and not the address of the slot.
                if matches!(self.get_pointee_ty(p), Ty::Ptr(_)) {
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

    fn get_struct_type(&mut self, path: &Path) -> StructType<'ctx> {
        let key = path.to_string();

        if let Some(st) = self.struct_types.get(&key) {
            return st.clone();
        }

        let opaque = self.lcx.opaque_struct_type(&key);
        self.struct_types.insert(key.clone(), opaque);

        let struct_ty = self
            .tcx
            .get_struct_ty(path)
            .expect("could not find struct type definition");

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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        // collect the function symbols
        let mut fn_map: HashMap<Path, &Node<lir::Func>> = HashMap::new();
        for func in self.funcs.iter() {
            match fn_map.entry(func.name.clone()) {
                Entry::Vacant(entry) => {
                    entry.insert(func);
                }
                Entry::Occupied(mut entry) => {
                    let existing = *entry.get();
                    let existing_weight =
                        existing.value.blocks.iter().map(|b| b.len()).sum::<usize>();
                    let new_weight = func.value.blocks.iter().map(|b| b.len()).sum::<usize>();
                    let existing_symbols = existing.value.symbols.len();
                    let new_symbols = func.value.symbols.len();
                    if new_weight > existing_weight
                        || (new_weight == existing_weight && new_symbols > existing_symbols)
                    {
                        entry.insert(func);
                    }
                }
            }
        }
        log::debug!("fn_map: {:#?}", fn_map.keys());

        let mut symbols = HashSet::new();
        let start_fn = &self.funcs[self.start_idx as usize];
        symbols.insert(start_fn.name.clone());
        collect_symbols(start_fn, &mut symbols, &fn_map);
        log::debug!("all symbols: {:?}", symbols);

        for ext in self.externs.iter() {
            if !symbols.contains(&ext.name) {
                continue;
            }

            // TODO: wrap in "is_intrinsic"
            if ext.name.to_short_name() == "sizeof" {
                continue;
            }

            // define
            log::debug!("define extern: {}", ext.name);
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
            let init_value = global.init_value.codegen(ctx, tcx, srcmap)?;
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

            if srcmap.has_inline(f) {
                let inline_attr = ctx
                    .lcx
                    .create_enum_attribute(Attribute::get_named_enum_kind_id("alwaysinline"), 0);
                fn_val.add_attribute(AttributeLoc::Function, inline_attr);
            }

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
            f.codegen(ctx, tcx, srcmap)?;
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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
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
        if ret_ty.is_aggregate() && !ret_ty.is_struct(tcx) {
            // First LLVM param is the sret pointer
            if let Some(retptr_val) = params_iter.next() {
                let retptr = retptr_val.into_pointer_value();
                ctx.sret_param = Some(retptr);
                ctx.register_pointee_ty(retptr, ret_ty.clone());
            }
        }
        for (param_val, param) in params_iter.zip(self.params.iter()) {
            param_val.set_name(&param.name);
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

            let alloca = ctx.alloca(ty)?;
            ctx.locals.insert(loc.idx, alloca);
        }

        // codegen each block as a basic block
        for block in self.blocks.iter() {
            let bb = ctx.get_block(block.label());
            ctx.builder.position_at_end(bb);
            block.codegen(ctx, tcx, srcmap)?;
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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'_, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        for i in self.deref() {
            let _ = i.codegen(ctx, tcx, srcmap)?;

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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        Ok(Some(match self {
            lir::Inst::StructInit(dst, _) => {
                // Destination must be a local slot. We store a freshly allocated
                // struct payload pointer into that slot.
                let slot = match dst {
                    lir::Variable::Local(idx) => ctx.get_local(*idx),
                    other => panic!("StructInit destination must be a local, got: {:?}", other),
                };

                // The slot for a struct local holds a pointer value (Ty::Ptr(struct_ty)).
                let slot_pointee = ctx.get_pointee_ty(slot).clone();
                let struct_ty = match slot_pointee {
                    Ty::Ptr(inner) => inner.as_ref().clone(),
                    ty => ty, // best effort: if already a struct type
                };

                // Resolve the LLVM payload type for the struct and allocate it.
                let fqn = struct_ty
                    .get_path()
                    .expect("struct type missing fully-qualified name");

                let struct_def = ctx.tcx.get_struct_ty(&fqn).unwrap();

                match struct_def.kind {
                    NominalKind::Struct => {
                        let llvm_struct = ctx.get_struct_type(&fqn);
                        let ptr = ctx
                            .builder
                            .build_malloc(llvm_struct, &format!("malloc:<*{}>", struct_ty))?;

                        // Track the pointee type of the allocated pointer as the struct type.
                        ctx.register_pointee_ty(ptr, struct_ty);

                        // Store the pointer VALUE into the local slot (which itself points to Ty::Ptr(...)).
                        let _ = ctx.builder.build_store(slot, ptr)?;
                    }
                    NominalKind::Record => { /* do nothing */ }
                }

                return Ok(None);
            }

            lir::Inst::Free(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Call(call) => {
                match call.codegen(ctx, tcx, srcmap)? {
                    LoweredCall::Value(_v) => {
                        // Intrinsic folded to a value in expression position; as a statement call,
                        // this becomes a no-op.
                        return Ok(None);
                    }
                    LoweredCall::Call { call, .. } => call
                        .try_as_basic_value()
                        .either(|val| val.as_instruction_value().unwrap(), |inst| inst),
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
                ctx.build_set_local(*idx, value, tcx, srcmap)?
            }
            lir::Inst::MemCopy(dest_var, src_var, size) => {
                ctx.build_memcpy(dest_var, src_var, size, tcx, srcmap)?
            }
            lir::Inst::Store(s) => s.codegen(ctx, tcx, srcmap)?,
            lir::Inst::SetField(s) => s.codegen(ctx, tcx, srcmap)?,
            lir::Inst::IncRef(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::DecRef(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Return(v) => {
                // Compute the value to return, then delegate to the typed-return helper.
                let ret_val = v.codegen(ctx, tcx, srcmap)?;
                let ret_ty = ctx.curr_ret_ty.clone().expect("missing curr_ret_ty");
                ctx.build_typed_return(&ret_ty, ret_val)?
            }
            // skip all of the control instructions (expect return), which will be processed later
            lir::Inst::Goto(idx) => {
                let bb = ctx.get_block(*idx);
                ctx.builder.build_unconditional_branch(bb)?
            }
            lir::Inst::Break(b) => b.codegen(ctx, tcx, srcmap)?,
            lir::Inst::If(if_expr) => if_expr.codegen(ctx, tcx, srcmap)?,
        }))
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Value {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        match self {
            lir::Value::VarRef(_) => {
                unreachable!("COMPILER BUG: this should be removed by this point")
            }
            lir::Value::Empty => Ok(ctx.unit()),
            lir::Value::Atom(a) => a.codegen(ctx, tcx, srcmap),
            lir::Value::Malloc(m) => m.codegen(ctx, tcx, srcmap),
            lir::Value::Call(c) => Ok(match c.codegen(ctx, tcx, srcmap)? {
                LoweredCall::Value(v) => v,
                LoweredCall::Call { call, ret_slot } => ret_slot
                    .map(|p| p.as_basic_value_enum())
                    .unwrap_or_else(|| call.try_as_basic_value().left_or_else(|_| ctx.unit())),
            }),
            lir::Value::CExternCall(_) => todo!("codegen lir::CExternCall: {}", self),
            lir::Value::Select(_) => todo!("codegen lir::Select: {}", self),
            lir::Value::Phi(phi) => phi.codegen(ctx, tcx, srcmap),
            lir::Value::Load(l) => l.codegen(ctx, tcx, srcmap),
            lir::Value::Lea(lea) => lea.codegen(ctx, tcx, srcmap),
            lir::Value::GetField(g) => g.codegen(ctx, tcx, srcmap),
            lir::Value::BasicOp(b) => b.codegen(ctx, tcx, srcmap),
            lir::Value::Cast(c) => c.codegen(ctx, tcx, srcmap),
            lir::Value::IntConvert(_) => todo!("codegen lir::IntConvert: {}", self),
            lir::Value::Type(_) => todo!("codegen lir::Type: {}", self),
        }
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Malloc {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let orig_ty = self.ty.mono();
        let element_ty = match orig_ty.clone() {
            Ty::Ptr(inner) => *inner,
            ty => ty,
        };

        let pointee_ty = if orig_ty.innermost().is_struct(tcx) {
            Ty::Ptr(Box::new(element_ty.clone()))
        } else {
            element_ty.clone()
        };

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
                let mut size_value = v.codegen(ctx, tcx, srcmap)?;
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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        log::debug!("[load] generating: {:?}", self);
        let mut ptr = self.src.codegen(ctx, tcx, srcmap)?.into_pointer_value();
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

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Store {
    type Output = Result<InstructionValue<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        match self.dst {
            lir::Variable::Data(..) => todo!(),
            lir::Variable::Global(..) => todo!(),
            lir::Variable::Local(idx) => {
                let mut ptr = ctx.get_local(idx);
                // if the local holds a pointer, we are storing to the pointee
                if matches!(ctx.get_pointee_ty(ptr), Ty::Ptr(_)) {
                    ptr = ctx.load_pointer(ptr)?.into_pointer_value();
                }

                if self.offset.ptrs > 0 {
                    ptr = ctx.get_element_ptr(ptr, self.offset.ptrs)?;
                }

                if self.offset.bytes > 0 {
                    ptr = ctx.byte_offset_ptr(ptr, self.offset.bytes)?;
                }

                let value = self.value.codegen(ctx, tcx, srcmap)?;
                ctx.store(ptr, value)
            }
            lir::Variable::Unit => todo!(),
        }
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Lea {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let ptr = match &self.offset {
            lir::LeaOffset::Const(offset) => {
                // generate the base pointer
                let var = self.var.codegen(ctx, tcx, srcmap)?;
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
            lir::LeaOffset::Field(_, field) => ctx.get_field_ptr(&self.var, field, tcx)?,
        };

        Ok(ptr.as_basic_value_enum())
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::If {
    type Output = Result<InstructionValue<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        _: &TyCtx,
        _: &SourceMap,
    ) -> Self::Output {
        let val = ctx.load_local(self.cond_loc)?.into_int_value();
        let then_block = ctx.get_block(self.then_label);
        let else_block = ctx.get_block(self.else_label);
        ctx.builder
            .build_conditional_branch(val, then_block, else_block)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Phi {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        _: &TyCtx,
        _: &SourceMap,
    ) -> Self::Output {
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

    fn codegen(&self, _: &mut LLVMCodegenCtx, _: &TyCtx, _: &SourceMap) -> Self::Output {
        unimplemented!("lir::Break::codegen")
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::GetField {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        _: &SourceMap,
    ) -> Self::Output {
        let ptr = ctx.get_field_ptr(&self.src, &self.field, tcx)?;

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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let ptr = ctx.get_field_ptr(&self.dst, &self.field, tcx)?;
        let field_ty = ctx.get_pointee_ty(ptr).clone();

        log::debug!(
            "[SetField] dst={:?} field={} ptr={} field_ty={}",
            self.dst,
            self.field,
            ptr.to_string(),
            field_ty
        );

        // If the field itself is an aggregate (struct/tuple/array), copy bytes via memcpy.
        let value = self.value.codegen(ctx, tcx, srcmap)?;
        if field_ty.is_aggregate() && !field_ty.is_struct(tcx) {
            log::debug!("[SetField] aggregate field; using memcpy");
            return ctx.memcpy_aggregate_from_value(ptr, &field_ty, value);
        }

        // Non-aggregate field: use regular store semantics (with pointer/value fixups).
        ctx.store(ptr, value)
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Cast {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let mut val = self.src.codegen(ctx, tcx, srcmap)?;
        val = ctx.maybe_load_pointer(val)?;

        let ty = ctx.to_llvm_type(&self.ty);
        log::debug!("{}", ty.print_to_string());
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
            _ => ctx
                .builder
                .build_bit_cast(val, ty, "")?
                .as_basic_value_enum(),
        })
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Call {
    type Output = Result<LoweredCall<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        // Intrinsic: sizeof(...)
        if self.fn_name.to_string() == "sizeof" {
            // One meta-type argument; compute size as ptr-width uint (matches Ray `uint`).
            let meta_ty = ctx.type_of(&self.args[0]).clone();
            let underlying_ty = meta_ty.get_ty_param_at(0);
            let ll = ctx.to_llvm_type(underlying_ty);
            let raw = ll.size_of().expect("could not compute sizeof for type");
            // Cast to target ptr-sized int (i32 on wasm32) so call sites see the right width.
            let cast = ctx
                .builder
                .build_int_cast(raw, ctx.ptr_type(), "")
                .expect("int cast for sizeof");
            return Ok(LoweredCall::Value(cast.as_basic_value_enum()));
        }

        // Marshal arguments using the same rule as Inst::Call.
        let function = *ctx.fn_index.get(&self.fn_name).expect(
            format!(
                "cannot find function `{}` in index for value-call",
                self.fn_name
            )
            .as_str(),
        );
        let fn_ty = function.get_type();
        let expected_params = fn_ty.get_param_types();

        // Look up callee to inspect its Ray type for sret decision.
        let ret_ty = self.callee_ty.mono().get_fn_ret_ty().unwrap_or_else(|| {
            panic!(
                "type for callee is not a function: {} ({})",
                self.fn_name, self.callee_ty
            )
        });
        if ret_ty.is_aggregate() && !ret_ty.is_struct(tcx) {
            let (call, ret_slot) =
                ctx.build_sret_call(function, &self.args, &expected_params, ret_ty, tcx, srcmap)?;
            return Ok(LoweredCall::Call {
                call,
                ret_slot: Some(ret_slot),
            });
        }

        // Non-aggregate: regular call and unwrap pointer args as needed.
        let call = ctx.build_call(function, &self.args, &expected_params, tcx, srcmap)?;
        Ok(LoweredCall::Call {
            call,
            ret_slot: None,
        })
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::BasicOp {
    type Output = Result<BasicValueEnum<'ctx>, BuilderError>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        // convert the lir op and size into a wasm op
        let operands = self
            .operands
            .codegen(ctx, tcx, srcmap)
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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        Ok(match self {
            lir::Atom::Variable(v) => v.codegen(ctx, tcx, srcmap)?,
            lir::Atom::FuncRef(_) => todo!("codegen lir::Atom: {}", self),
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

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        _: &TyCtx,
        _: &SourceMap,
    ) -> Self::Output {
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
