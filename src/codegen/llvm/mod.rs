mod attr;

use std::{
    collections::{HashMap, HashSet},
    env::{self, temp_dir},
    fs,
    io::Write,
    ops::Deref,
};

use inkwell as llvm;
use llvm::{
    attributes::AttributeLoc,
    basic_block::BasicBlock,
    module::Linkage,
    passes::{PassManager, PassManagerBuilder},
    targets::{FileType, InitializationConfig, Target, TargetMachine, TargetTriple},
    types::{AnyType, AnyTypeEnum, BasicType, BasicTypeEnum, IntType, StructType},
    values::{
        AnyValue, BasicValue, BasicValueEnum, FunctionValue, GlobalValue, InstructionOpcode,
        InstructionValue, IntValue, PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};
use rand::Rng;

use crate::{
    ast::{Modifier, Path},
    codegen::collect_symbols,
    errors::RayError,
    lir,
    pathlib::FilePath,
    span::SourceMap,
    typing::{ty::Ty, TyCtx},
};

use super::Codegen;

use attr::Attribute;

static MALLOC_BUF: &'static [u8] = include_bytes!("../../../lib/libc/wasi_malloc.wasm");

lazy_static! {
    static ref MALLOC_BUF_HASH: u64 = xxhash_rust::xxh3::xxh3_64(MALLOC_BUF);
}

pub fn codegen<'a, 'ctx, P>(
    program: &lir::Program,
    tcx: &TyCtx,
    srcmap: &SourceMap,
    lcx: &'a llvm::context::Context,
    output_path: P,
) -> Result<(), Vec<RayError>>
where
    P: FnOnce(&'static str) -> FilePath,
{
    let name = program.module_path.to_string();
    let module = lcx.create_module(&name);
    let builder = lcx.create_builder();
    let mut ctx = LLVMCodegenCtx::new(lcx, &module, &builder);
    program.codegen(&mut ctx, tcx, srcmap);

    if let Err(err) = module.verify() {
        panic!(
            "COMPILER BUG: {}\n{}",
            err.to_string(),
            module.print_to_string().to_string()
        );
    }

    let pm_builder = PassManagerBuilder::create();
    pm_builder.set_optimization_level(OptimizationLevel::None);

    let pm = PassManager::create(());
    pm.add_promote_memory_to_register_pass();
    pm.add_instruction_simplify_pass();
    pm.add_memcpy_optimize_pass();
    pm.add_cfg_simplification_pass();
    pm.add_licm_pass();
    pm.add_dead_arg_elimination_pass();
    pm.add_dead_store_elimination_pass();
    pm.add_always_inliner_pass();

    ctx.target_machine.add_analysis_passes(&pm);
    pm_builder.populate_module_pass_manager(&pm);
    pm.run_on(&module);

    if let Err(err) = module.verify() {
        panic!(
            "COMPILER BUG: {}\n{}",
            err.to_string(),
            module.print_to_string().to_string()
        );
    }

    // write out the object to a temp file
    let mut rng = rand::thread_rng();
    let id = rng.gen::<u64>();
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
    lld::link(&[
        str!("wasm-ld"),
        obj_path.to_string(),
        malloc_path.to_string(),
        str!("--no-entry"),
        str!("-o"),
        curr_dir.join(wasm_path).to_str().unwrap().to_string(),
    ])
    .ok()
    .unwrap();
    Ok(())
}

fn to_basic_type(ty: AnyTypeEnum) -> BasicTypeEnum {
    match ty {
        AnyTypeEnum::ArrayType(t) => t.as_basic_type_enum(),
        AnyTypeEnum::FloatType(t) => t.as_basic_type_enum(),
        AnyTypeEnum::IntType(t) => t.as_basic_type_enum(),
        AnyTypeEnum::PointerType(t) => t.as_basic_type_enum(),
        AnyTypeEnum::StructType(t) => t.as_basic_type_enum(),
        AnyTypeEnum::VectorType(t) => t.as_basic_type_enum(),
        AnyTypeEnum::FunctionType(_) | AnyTypeEnum::VoidType(_) => panic!("not a basic type"),
    }
}

struct LLVMCodegenCtx<'a, 'ctx> {
    lcx: &'ctx llvm::context::Context,
    module: &'a llvm::module::Module<'ctx>,
    builder: &'a llvm::builder::Builder<'ctx>,
    target_machine: TargetMachine,
    curr_fn: Option<FunctionValue<'ctx>>,
    fn_index: HashMap<Path, FunctionValue<'ctx>>,
    struct_types: HashMap<String, StructType<'ctx>>,
    data_addrs: HashMap<usize, GlobalValue<'ctx>>,
    globals: HashMap<usize, GlobalValue<'ctx>>,
    locals: HashMap<usize, PointerValue<'ctx>>,
    local_tys: Vec<Ty>,
    blocks: HashMap<usize, BasicBlock<'ctx>>,
}

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    fn new(
        lcx: &'ctx llvm::context::Context,
        module: &'a llvm::module::Module<'ctx>,
        builder: &'a llvm::builder::Builder<'ctx>,
    ) -> Self {
        Target::initialize_webassembly(&InitializationConfig::default());
        // TODO: make this variable?
        let target = Target::from_name("wasm32").expect("could not get wasm32 target");
        let target_machine = target
            .create_target_machine(
                &TargetTriple::create("wasm32-wasi"),
                "generic",
                "",
                llvm::OptimizationLevel::Default,
                llvm::targets::RelocMode::Default,
                llvm::targets::CodeModel::Default,
            )
            .expect("could not create wasm32-wasi target machine");

        let target_data = target_machine.get_target_data();
        let data_layout = target_data.get_data_layout();
        module.set_data_layout(&data_layout);

        Self {
            lcx,
            module,
            builder,
            target_machine,
            curr_fn: None,
            fn_index: HashMap::new(),
            struct_types: HashMap::new(),
            data_addrs: HashMap::new(),
            globals: HashMap::new(),
            locals: HashMap::new(),
            local_tys: vec![],
            blocks: HashMap::new(),
        }
    }

    fn type_of(&self, var: &lir::Variable) -> &Ty {
        match var {
            lir::Variable::Unit => panic!("unit is untyped"),
            lir::Variable::Data(_) => panic!("data is untyped"),
            lir::Variable::Global(idx) => {
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

    fn is_indexable(&self, ptr: PointerValue<'ctx>) -> bool {
        let ptr_el_ty = ptr.get_type().get_element_type();
        return matches!(
            ptr_el_ty,
            AnyTypeEnum::ArrayType(_)
                | AnyTypeEnum::PointerType(_)
                | AnyTypeEnum::StructType(_)
                | AnyTypeEnum::VectorType(_)
        );
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

    fn load_local(&self, idx: usize) -> BasicValueEnum<'ctx> {
        let ptr = self.get_local(idx);
        self.builder.build_load(ptr, "")
    }

    fn get_local_llvm_ty(&self, idx: usize) -> BasicTypeEnum<'ctx> {
        let ptr = self.get_local(idx);
        to_basic_type(ptr.get_type().get_element_type())
    }

    fn get_field_ptr(
        &self,
        var: &lir::Variable,
        field: &String,
        tcx: &TyCtx,
    ) -> PointerValue<'ctx> {
        // get the field offset and size
        let lhs_ty = self.type_of(var);
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

        // TODO: what to do about size???
        let offset = self.ptr_type().const_int(offset, false);
        match var {
            lir::Variable::Data(_) => todo!(),
            lir::Variable::Global(_) => todo!(),
            lir::Variable::Local(idx) => {
                let ptr = self.load_local(*idx).into_pointer_value();
                unsafe { self.builder.build_gep(ptr, &[self.zero(), offset], "") }
            }
            lir::Variable::Unit => todo!(),
        }
    }

    fn to_llvm_type(&mut self, ty: &Ty, tcx: &TyCtx) -> BasicTypeEnum<'ctx> {
        match ty {
            Ty::Never => todo!("to_llvm_ty: {}", ty),
            Ty::Func(_, _) => todo!("to_llvm_ty: {}", ty),
            Ty::Var(_) | Ty::Any => BasicTypeEnum::IntType(self.ptr_type()),
            Ty::Tuple(tys) => BasicTypeEnum::StructType(
                self.lcx.struct_type(
                    tys.iter()
                        .map(|ty| self.to_llvm_type(ty, tcx))
                        .collect::<Vec<_>>()
                        .as_slice(),
                    false,
                ),
            ),
            Ty::Union(_) | Ty::Array(..) => todo!("to_llvm_ty: {}", ty),
            Ty::Ptr(pointee_ty) => BasicTypeEnum::PointerType(
                self.to_llvm_type(pointee_ty, tcx)
                    .ptr_type(AddressSpace::Generic),
            ),
            Ty::Projection(fqn, ..) => match fqn.as_str() {
                "bool" => BasicTypeEnum::IntType(self.lcx.bool_type()),
                "i8" | "u8" => BasicTypeEnum::IntType(self.lcx.i8_type()),
                "i16" | "u16" => BasicTypeEnum::IntType(self.lcx.i16_type()),
                "i32" | "u32" | "char" => BasicTypeEnum::IntType(self.lcx.i32_type()),
                "u64" | "i64" => BasicTypeEnum::IntType(self.lcx.i64_type()),
                "int" | "uint" => BasicTypeEnum::IntType(self.ptr_type()),
                fqn => BasicTypeEnum::PointerType(
                    BasicTypeEnum::StructType(self.get_struct_type(fqn, tcx))
                        .ptr_type(AddressSpace::Generic),
                ),
            },
            Ty::Cast(_, _) => todo!("to_llvm_ty: {}", ty),
            Ty::Qualified(_, _) => todo!("to_llvm_ty: {}", ty),
            Ty::All(_, _) => todo!("to_llvm_ty: {}", ty),
        }
    }

    fn alloca(&mut self, ty: &Ty, tcx: &TyCtx) -> PointerValue<'ctx> {
        let entry = self.get_fn().get_first_basic_block().unwrap();

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

        let ty = self.to_llvm_type(ty, tcx);
        self.builder.build_alloca(ty, "")
    }

    fn load(&self, val: BasicValueEnum<'a>) -> BasicValueEnum<'a> {
        if let BasicValueEnum::PointerValue(ptr) = val {
            self.builder.build_load(ptr, "").as_basic_value_enum()
        } else {
            val
        }
    }

    fn store(
        &self,
        ptr: PointerValue<'ctx>,
        mut value: BasicValueEnum<'a>,
    ) -> InstructionValue<'a> {
        // if to_basic_type(ptr.get_type().get_element_type())
        //             != value.get_type().as_basic_type_enum()
        //         {

        if let BasicValueEnum::PointerValue(rhs_ptr) = value {
            if rhs_ptr.get_type() == ptr.get_type() {
                value = self.builder.build_load(rhs_ptr, "").as_basic_value_enum();
            }
        }
        self.builder.build_store(ptr, value)
    }

    fn fn_attr(&self, fn_val: FunctionValue<'ctx>, key: &str, val: &str) {
        let attribute = self.lcx.create_string_attribute(key, val);
        fn_val.add_attribute(AttributeLoc::Function, attribute);
    }

    fn get_struct_type(&mut self, fqn: &str, tcx: &TyCtx) -> StructType<'ctx> {
        if !self.struct_types.contains_key(fqn) {
            let opaque = self.lcx.opaque_struct_type(&fqn);
            let path = Path::from(fqn);
            let struct_ty = tcx.get_struct_ty(&path).unwrap();

            opaque.set_body(
                struct_ty
                    .fields
                    .iter()
                    .map(|(_, ty)| self.to_llvm_type(ty, tcx))
                    .collect::<Vec<_>>()
                    .as_slice(),
                false,
            );
            self.struct_types.insert(fqn.to_string(), opaque);
        }

        self.struct_types.get(fqn).unwrap().clone()
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Program {
    type Output = ();

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        // collect the function symbols
        let fn_map = self
            .funcs
            .iter()
            .map(|f| (f.name.clone(), f))
            .collect::<HashMap<_, _>>();
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
            // define
            log::debug!("define extern: {}", ext.name);
            if let Ok((_, _, param_tys, ret_ty)) = ext.ty.try_borrow_fn() {
                let ret_ty = ctx.to_llvm_type(ret_ty, tcx);
                let fn_ty = ret_ty.fn_type(
                    param_tys
                        .iter()
                        .map(|ty| ctx.to_llvm_type(ty, tcx))
                        .collect::<Vec<_>>()
                        .as_slice(),
                    false,
                );
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
                Some(AddressSpace::Generic),
                d.name(),
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

            ctx.data_addrs.insert(d.index(), global);
        }

        for global in self.globals.iter() {
            let global_type = ctx.to_llvm_type(&global.ty, tcx);
            let global_val =
                ctx.module
                    .add_global(global_type, Some(AddressSpace::Generic), &global.name);
            let init_value = global.init_value.codegen(ctx, tcx, srcmap);
            global_val.set_initializer(&init_value);

            ctx.globals.insert(global.idx, global_val);
        }

        let mut funcs = vec![];
        for (i, f) in self.funcs.iter().enumerate() {
            if !symbols.contains(&f.name) {
                // don't generate functions that are not in the symbol set
                continue;
            }

            let (_, _, param_tys, ret_ty) = f.ty.try_borrow_fn().unwrap();
            let ret_ty = ctx.to_llvm_type(ret_ty, tcx);
            let fn_ty = ret_ty.fn_type(
                param_tys
                    .iter()
                    .map(|ty| ctx.to_llvm_type(ty, tcx))
                    .collect::<Vec<_>>()
                    .as_slice(),
                false,
            );

            let name = f.name.to_mangled();
            let fn_val = ctx.module.add_function(&name, fn_ty, None);
            if f.modifiers.contains(&Modifier::Wasi) {
                ctx.fn_attr(fn_val, "wasm-import-module", "wasi_snapshot_preview1");
                ctx.fn_attr(fn_val, "wasm-import-name", &name);
            }

            if f.name.to_string() != "_start" {
                fn_val.set_linkage(Linkage::Internal);
            } else {
                ctx.fn_attr(fn_val, "wasm-export-name", "_start");
            }

            if srcmap.has_inline(f) {
                let inline_attr = ctx
                    .lcx
                    .create_enum_attribute(0, Attribute::ALWAYS_INLINE.bits());
                fn_val.add_attribute(AttributeLoc::Function, inline_attr);
            }

            ctx.fn_index.insert(f.name.clone(), fn_val);
            funcs.push((i, fn_val));
        }

        for (i, val) in funcs {
            let f = &self.funcs[i];
            if srcmap.has_inline(f) {
                // don't generate inline functions
                continue;
            }

            let local_tys = f
                .locals
                .iter()
                .map(|loc| loc.ty.clone())
                .collect::<Vec<_>>();
            ctx.local_tys = local_tys;
            ctx.curr_fn = Some(val);
            f.codegen(ctx, tcx, srcmap);
        }

        if let Some(malloc_fn) = ctx.module.get_function("malloc") {
            // use the __wasi_malloc import for malloc
            malloc_fn.as_global_value().set_name("__wasi_malloc");
        }
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Func {
    type Output = ();

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        log::debug!("generating {}", self);

        // clear the locals and blocks
        ctx.locals.clear();
        ctx.blocks.clear();

        // create the local types
        ctx.local_tys = self.locals.iter().map(|l| l.ty.clone()).collect();

        // create the function value
        let fn_val = *ctx.fn_index.get(&self.name).unwrap();
        ctx.curr_fn = Some(fn_val);
        ctx.fn_index.insert(self.name.clone(), fn_val);

        // initialize the entry block with arguments
        let entry = ctx.lcx.append_basic_block(fn_val, "entry");
        ctx.builder.position_at_end(entry);

        for (param_val, param) in fn_val.get_param_iter().zip(self.params.iter()) {
            param_val.set_name(&param.name);
            let alloca = ctx.alloca(&param.ty, tcx);
            ctx.builder.build_store(alloca, param_val);
            ctx.locals.insert(param.idx, alloca);
            log::debug!("adding local parameter {} (${})", param.name, param.idx);
        }

        for loc in self.locals.iter() {
            if loc.idx < self.params.len() {
                continue;
            }

            let alloca = ctx.alloca(&loc.ty, tcx);
            ctx.locals.insert(loc.idx, alloca);
            log::debug!("adding local ${}", loc.idx);
        }

        // codegen each block as a basic block
        for block in self.blocks.iter() {
            let bb = ctx.get_block(block.label());
            ctx.builder.position_at_end(bb);
            block.codegen(ctx, tcx, srcmap);
        }

        // add a branch from entry block to first block
        if let Some(first_block) = self.blocks.first() {
            let dest = ctx.get_block(first_block.label());
            ctx.builder.position_at_end(entry);
            ctx.builder.build_unconditional_branch(dest);
        }
    }
}

impl Codegen<LLVMCodegenCtx<'_, '_>> for lir::Block {
    type Output = ();

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'_, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        for i in self.deref() {
            i.codegen(ctx, tcx, srcmap);
        }
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Inst {
    type Output = InstructionValue<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        match self {
            lir::Inst::Free(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Call(call) => call
                .codegen(ctx, tcx, srcmap)
                .as_instruction_value()
                .unwrap(),
            lir::Inst::CExternCall(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetGlobal(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetLocal(idx, value) => {
                let ptr = ctx.get_local(*idx);
                let value = value.codegen(ctx, tcx, srcmap);
                ctx.store(ptr, value)
            }
            lir::Inst::MemCopy(dest_var, src_var, size) => {
                let mut dest = dest_var.codegen(ctx, tcx, srcmap).into_pointer_value();
                if dest_var.is_local() {
                    dest = ctx.builder.build_load(dest, "").into_pointer_value();
                }

                let mut src = src_var.codegen(ctx, tcx, srcmap).into_pointer_value();
                if src_var.is_local() {
                    src = ctx.builder.build_load(src, "").into_pointer_value();
                }
                let size = size.codegen(ctx, tcx, srcmap).into_int_value();
                ctx.builder
                    .build_memcpy(dest, 2, src, 2, size)
                    .unwrap()
                    .as_instruction_value()
                    .unwrap()
            }
            lir::Inst::Store(s) => s.codegen(ctx, tcx, srcmap),
            lir::Inst::SetField(s) => s.codegen(ctx, tcx, srcmap),
            lir::Inst::IncRef(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::DecRef(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Return(v) => {
                let mut val = v.codegen(ctx, tcx, srcmap);
                if val.is_pointer_value() {
                    let ptr = val.into_pointer_value();
                    val = ctx.builder.build_load(ptr, "").as_basic_value_enum();
                }
                ctx.builder.build_return(Some(&val))
            }
            // skip all of the control instructions (expect return), which will be processed later
            lir::Inst::Goto(idx) => {
                let bb = ctx.get_block(*idx);
                ctx.builder.build_unconditional_branch(bb)
            }
            lir::Inst::Break(b) => b.codegen(ctx, tcx, srcmap),
            lir::Inst::If(if_expr) => if_expr.codegen(ctx, tcx, srcmap),
        }
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Value {
    type Output = BasicValueEnum<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        match self {
            lir::Value::VarRef(_) => {
                unreachable!("COMPILER BUG: this should be removed by this point")
            }
            lir::Value::Empty => ctx.unit(),
            lir::Value::Atom(a) => a.codegen(ctx, tcx, srcmap),
            lir::Value::Malloc(m) => m.codegen(ctx, tcx, srcmap),
            lir::Value::Call(c) => c.codegen(ctx, tcx, srcmap),
            lir::Value::CExternCall(_) => todo!("codegen lir::CExternCall: {}", self),
            lir::Value::Select(_) => todo!("codegen lir::Select: {}", self),
            lir::Value::Phi(phi) => phi.codegen(ctx, tcx, srcmap),
            lir::Value::Load(l) => l.codegen(ctx, tcx, srcmap),
            lir::Value::Lea(_) => todo!("codegen lir::Lea: {}", self),
            lir::Value::GetField(g) => g.codegen(ctx, tcx, srcmap),
            lir::Value::BasicOp(b) => b.codegen(ctx, tcx, srcmap),
            lir::Value::Cast(c) => c.codegen(ctx, tcx, srcmap),
            lir::Value::IntConvert(_) => todo!("codegen lir::IntConvert: {}", self),
        }
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Malloc {
    type Output = BasicValueEnum<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let mut ty = ctx.to_llvm_type(&self.ty, tcx);
        if let BasicTypeEnum::PointerType(ptr_ty) = ty {
            ty = to_basic_type(ptr_ty.get_element_type())
        }

        let size = match &self.count {
            lir::Atom::Variable(v) => {
                let mut size_value = v.codegen(ctx, tcx, srcmap);
                size_value = ctx.load(size_value);
                if let BasicValueEnum::PointerValue(ptr) = size_value {
                    size_value = ctx.builder.build_load(ptr, "").as_basic_value_enum();
                }
                size_value
            }
            &lir::Atom::UintConst(count, _) => {
                if count == 1 {
                    return ctx
                        .builder
                        .build_malloc(ty, "")
                        .unwrap()
                        .as_basic_value_enum();
                }

                ctx.ptr_type().const_int(count, false).as_basic_value_enum()
            }
            lir::Atom::Size(_) => todo!(),
            lir::Atom::FuncRef(_)
            | lir::Atom::BoolConst(_)
            | lir::Atom::CharConst(_)
            | lir::Atom::IntConst(_, _)
            | lir::Atom::FloatConst(_, _)
            | lir::Atom::RawString(_)
            | lir::Atom::NilConst => panic!(
                "COMPILER BUG: invalid count expression for lir::Malloc: {}",
                self.count
            ),
        };

        ctx.builder
            .build_array_malloc(ty, size.into_int_value(), "")
            .unwrap()
            .as_basic_value_enum()
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Load {
    type Output = BasicValueEnum<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        // TODO: what to do about size?
        let offset = ctx.size_to_int(&self.offset);
        let mut ptr = self.src.codegen(ctx, tcx, srcmap).into_pointer_value();
        ptr = unsafe { ctx.builder.build_gep(ptr, &[ctx.zero(), offset], "") };
        ptr.as_basic_value_enum()
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Store {
    type Output = InstructionValue<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        // TODO: what to do about size?
        let offset = ctx.size_to_int(&self.offset);
        match self.dst {
            lir::Variable::Data(_) => todo!(),
            lir::Variable::Global(_) => todo!(),
            lir::Variable::Local(idx) => {
                let mut ptr = ctx.get_local(idx);
                log::debug!("ptr = {}", ptr.print_to_string());
                if ctx.is_indexable(ptr) {
                    ptr = ctx.builder.build_load(ptr, "").into_pointer_value();
                }

                log::debug!("ptr = {}", ptr.print_to_string());
                if ctx.is_indexable(ptr) {
                    ptr = unsafe { ctx.builder.build_gep(ptr, &[ctx.zero(), offset], "") };
                }

                let value = self.value.codegen(ctx, tcx, srcmap);
                ctx.store(ptr, value)
            }
            lir::Variable::Unit => todo!(),
        }
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::If {
    type Output = InstructionValue<'a>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, '_>, _: &TyCtx, _: &SourceMap) -> Self::Output {
        let val = ctx.load_local(self.cond_loc).into_int_value();
        let then_block = ctx.get_block(self.then_label);
        let else_block = ctx.get_block(self.else_label);
        ctx.builder
            .build_conditional_branch(val, then_block, else_block)
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Phi {
    type Output = BasicValueEnum<'a>;

    fn codegen(&self, ctx: &mut LLVMCodegenCtx<'a, '_>, _: &TyCtx, _: &SourceMap) -> Self::Output {
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

        let phi = ctx.builder.build_phi(ty, "");
        for &(block_idx, loc_idx) in values {
            let bb = ctx.get_block(block_idx);
            if let Some(last) = bb.get_last_instruction() {
                // position before because the last instruction is an exit
                ctx.builder.position_before(&last);
            } else {
                ctx.builder.position_at_end(bb);
            }
            let val = ctx.load_local(loc_idx);
            phi.add_incoming(&[(&val, bb)]);
        }

        // position the builder back at the end of the block
        ctx.builder.position_at_end(curr_block);

        phi.as_basic_value()
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Break {
    type Output = InstructionValue<'a>;

    fn codegen(&self, _: &mut LLVMCodegenCtx, _: &TyCtx, _: &SourceMap) -> Self::Output {
        unimplemented!("lir::Break::codegen")
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::GetField {
    type Output = BasicValueEnum<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        _: &SourceMap,
    ) -> Self::Output {
        ctx.get_field_ptr(&self.src, &self.field, tcx)
            .as_basic_value_enum()
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::SetField {
    type Output = InstructionValue<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let ptr = ctx.get_field_ptr(&self.dst, &self.field, tcx);
        let value = self.value.codegen(ctx, tcx, srcmap);
        ctx.store(ptr, value)
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Cast {
    type Output = BasicValueEnum<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let mut val = self.src.codegen(ctx, tcx, srcmap);
        if let BasicValueEnum::PointerValue(ptr) = val {
            val = ctx.builder.build_load(ptr, "").as_basic_value_enum();
        }

        let ty = ctx.to_llvm_type(&self.ty, tcx);
        log::debug!("{}", ty.print_to_string());
        match (val, ty) {
            (BasicValueEnum::IntValue(int_val), BasicTypeEnum::PointerType(ptr_type)) => ctx
                .builder
                .build_int_to_ptr(int_val, ptr_type, "")
                .as_basic_value_enum(),
            (BasicValueEnum::PointerValue(ptr_val), BasicTypeEnum::IntType(int_type)) => ctx
                .builder
                .build_ptr_to_int(ptr_val, int_type, "")
                .as_basic_value_enum(),
            (BasicValueEnum::IntValue(int_val), _) => ctx
                .builder
                .build_int_cast(int_val, ty.into_int_type(), "")
                .as_basic_value_enum(),
            _ => ctx.builder.build_bitcast(val, ty, "").as_basic_value_enum(),
        }
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Call {
    type Output = BasicValueEnum<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        let function = *ctx.fn_index.get(&self.fn_name).expect(
            format!(
                "cannot find function `{}` in index: {:#?}",
                self.fn_name,
                ctx.fn_index.keys()
            )
            .as_str(),
        );

        let args = self
            .args
            .codegen(ctx, tcx, srcmap)
            .into_iter()
            .map(|val| {
                if let BasicValueEnum::PointerValue(ptr) = val {
                    ctx.builder.build_load(ptr, "").as_basic_value_enum()
                } else {
                    val
                }
            })
            .collect::<Vec<_>>();
        ctx.builder
            .build_call(function, args.as_slice(), "")
            .try_as_basic_value()
            .unwrap_left()
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::BasicOp {
    type Output = BasicValueEnum<'a>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        // convert the lir op and size into a wasm op
        let operands = self
            .operands
            .codegen(ctx, tcx, srcmap)
            .into_iter()
            .map(|op| {
                // unwrap any pointers
                if let BasicValueEnum::PointerValue(ptr) = op {
                    ctx.builder.build_load(ptr, "").as_basic_value_enum()
                } else {
                    op
                }
            })
            .collect::<Vec<_>>();

        match (self.op, self.signed) {
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
        }
        .as_basic_value_enum()
    }
}

impl<'a> Codegen<LLVMCodegenCtx<'a, '_>> for lir::Atom {
    type Output = BasicValueEnum<'a>; //BasicValue<'ctx>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, '_>,
        tcx: &TyCtx,
        srcmap: &SourceMap,
    ) -> Self::Output {
        match self {
            lir::Atom::Variable(v) => v.codegen(ctx, tcx, srcmap),
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
        }
    }
}

impl<'a, 'ctx> Codegen<LLVMCodegenCtx<'a, 'ctx>> for lir::Variable {
    type Output = BasicValueEnum<'a>; //Box<dyn BasicValue<'ctx>>;

    fn codegen(
        &self,
        ctx: &mut LLVMCodegenCtx<'a, 'ctx>,
        _: &TyCtx,
        _: &SourceMap,
    ) -> Self::Output {
        match self {
            lir::Variable::Data(idx) => ctx
                .data_addrs
                .get(idx)
                .unwrap()
                .as_pointer_value()
                .as_basic_value_enum(),
            lir::Variable::Global(idx) => ctx
                .globals
                .get(idx)
                .unwrap()
                .as_pointer_value()
                .as_basic_value_enum(),
            lir::Variable::Local(idx) => ctx.get_local(*idx).as_basic_value_enum(),
            lir::Variable::Unit => ctx.unit(),
        }
    }
}
