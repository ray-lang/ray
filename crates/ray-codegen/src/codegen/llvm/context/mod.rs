pub(crate) mod builtins;
pub(crate) mod calls;
pub(crate) mod panic_unwind;
pub(crate) mod rc;
pub(crate) mod stderr;

use std::collections::HashMap;

use inkwell::{self as llvm, builder::BuilderError, types::BasicMetadataTypeEnum};
use llvm::{
    AddressSpace,
    attributes::AttributeLoc,
    basic_block::BasicBlock,
    module::Linkage,
    targets::{InitializationConfig, Target as LLVMTarget, TargetMachine, TargetTriple},
    types::{BasicType, BasicTypeEnum, IntType, StructType},
    values::{
        BasicValue, BasicValueEnum, FunctionValue, GlobalValue, InstructionOpcode,
        InstructionValue, IntValue, PointerValue,
    },
};
use ray_core::{sourcemap::SourceMap, target::Target};
use ray_lir::{self as lir};
use ray_shared::{
    pathlib::{ItemPath, Path},
    ty::{Ty, TyVar},
};
use ray_typing::types::{EnumTy, StructTy, Subst, Substitutable};

use crate::codegen::Codegen as _;

/// Maximum number of stack trace entries collected during panic unwinding.
pub(crate) const MAX_TRACE_DEPTH: u32 = 32;

pub(crate) struct LLVMCodegenCtx<'a, 'ctx> {
    pub(crate) lcx: &'ctx llvm::context::Context,
    pub(crate) module: &'a llvm::module::Module<'ctx>,
    pub(crate) builder: &'a llvm::builder::Builder<'ctx>,
    pub(crate) target_machine: TargetMachine,
    pub(crate) curr_fn: Option<FunctionValue<'ctx>>,
    pub(crate) curr_ret_ty: Option<Ty>,
    pub(crate) fn_index: HashMap<Path, FunctionValue<'ctx>>,
    /// LLVM struct type cache - maps ray types to LLVM struct types.
    pub(crate) struct_types: HashMap<Ty, StructType<'ctx>>,
    pub(crate) data_addrs: HashMap<(Path, usize), GlobalValue<'ctx>>,
    pub(crate) globals: HashMap<(Path, usize), GlobalValue<'ctx>>,
    pub(crate) locals: HashMap<usize, PointerValue<'ctx>>,
    pub(crate) local_tys: Vec<Ty>,
    pub(crate) blocks: HashMap<usize, BasicBlock<'ctx>>,
    pub(crate) pointee_tys: HashMap<PointerValue<'ctx>, Ty>,
    pub(crate) sret_param: Option<PointerValue<'ctx>>,
    pub(crate) intrinsics: HashMap<Path, lir::IntrinsicKind>,
    /// Struct definitions from the program (both workspace and synthetic).
    pub(crate) struct_defs: &'a HashMap<ItemPath, StructTy>,
    /// Enum definitions from the program.
    pub(crate) enum_defs: &'a HashMap<ItemPath, EnumTy>,
    /// Pointer to the compiler-internal `__thread_ctx` global (panic/recover state).
    pub(crate) thread_ctx: Option<PointerValue<'ctx>>,
}

impl<'a, 'ctx> LLVMCodegenCtx<'a, 'ctx> {
    pub(crate) fn new(
        target: &Target,
        lcx: &'ctx llvm::context::Context,
        module: &'a llvm::module::Module<'ctx>,
        builder: &'a llvm::builder::Builder<'ctx>,
        struct_defs: &'a HashMap<ItemPath, StructTy>,
        enum_defs: &'a HashMap<ItemPath, EnumTy>,
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
            enum_defs,
            thread_ctx: None,
        }
    }

    pub(crate) fn type_of(&self, var: &lir::Variable) -> &Ty {
        match var {
            lir::Variable::Unit => panic!("unit is untyped"),
            lir::Variable::Data(..) => panic!("data is untyped"),
            lir::Variable::Global(_, idx) => {
                todo!("type of global: {}", idx)
            }
            lir::Variable::Local(idx) => &self.local_tys[*idx],
        }
    }

    pub(crate) fn ptr_type(&self) -> IntType<'ctx> {
        let target_data = self.target_machine.get_target_data();
        self.lcx.ptr_sized_int_type(&target_data, None)
    }

    pub(crate) fn unit_type(&self) -> StructType<'ctx> {
        self.lcx.struct_type(&[], false)
    }

    pub(crate) fn zero(&self) -> IntValue<'ctx> {
        self.ptr_type().const_zero()
    }

    pub(crate) fn unit(&self) -> BasicValueEnum<'ctx> {
        self.unit_type()
            .const_named_struct(&[])
            .as_basic_value_enum()
    }

    pub(crate) fn size_to_int(&self, s: &lir::Size) -> IntValue<'ctx> {
        let ptr_type = self.ptr_type();
        let ptr_size = ptr_type.size_of();
        let ptr_component = self
            .builder
            .build_int_mul(ptr_size, ptr_type.const_int(s.ptrs as u64, false), "")
            .unwrap();
        self.builder
            .build_int_add(ptr_component, ptr_type.const_int(s.bytes as u64, false), "")
            .unwrap()
    }

    pub(crate) fn size_to_type(&self, s: &lir::Size) -> IntType<'ctx> {
        match s {
            lir::Size { bytes: 0, ptrs: 1 } | lir::Size { bytes: 0, ptrs: 0 } => self.ptr_type(),
            lir::Size { bytes: 8, ptrs: 0 } => self.lcx.i64_type(),
            lir::Size { bytes: 4, ptrs: 0 } => self.lcx.i32_type(),
            lir::Size { bytes: 2, ptrs: 0 } => self.lcx.i16_type(),
            lir::Size { bytes: 1, ptrs: 0 } => self.lcx.i8_type(),
            _ => panic!("cannot create int type of size: {}", s),
        }
    }

    pub(crate) fn get_pointee_ty(&self, ptr: PointerValue<'ctx>) -> &Ty {
        self.pointee_tys.get(&ptr).unwrap()
    }

    pub(crate) fn register_pointee_ty(&mut self, ptr: PointerValue<'ctx>, ty: Ty) {
        log::debug!("[register_pointee_ty] ptr={} ty={}", ptr.to_string(), ty);
        self.pointee_tys.insert(ptr, ty);
    }

    pub(crate) fn lookup_struct_ty(&self, path: &ItemPath) -> &StructTy {
        self.struct_defs
            .get(path)
            .expect(&format!("could not find struct type: {}", path))
    }

    pub(crate) fn lookup_struct_ty_instantiated(
        &self,
        def_path: &ItemPath,
        args: &[Ty],
    ) -> StructTy {
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

    pub(crate) fn is_struct(&self, ty: &Ty) -> bool {
        if let Some(path) = ty.item_path() {
            self.struct_defs.contains_key(path)
        } else {
            false
        }
    }

    /// Whether a type uses reference counting (has a refcount header on the heap).
    /// `*T`, `*mut T`, and `id *T` are refcounted. `rawptr[T]`, `&T`, `&mut T` are not.
    pub(crate) fn is_refcounted_alloc(ty: &Ty) -> bool {
        matches!(ty, Ty::Ref(_) | Ty::MutRef(_) | Ty::IdRef(_))
    }

    /// Return `size_of(llvm_ty)` as a `ptr_type()`-width integer.
    ///
    /// LLVM's `size_of()` always returns `i64`, but on wasm32 our allocator
    /// functions (`__wasi_alloc`, `__wasi_dealloc`) and pointer arithmetic use
    /// `i32`. This helper casts the result so it matches `ptr_type()`.
    pub(crate) fn llvm_size_of(
        &self,
        llvm_ty: BasicTypeEnum<'ctx>,
        name: &str,
    ) -> Result<IntValue<'ctx>, BuilderError> {
        let raw = llvm_ty.size_of().expect("sized type");
        self.builder.build_int_cast(raw, self.ptr_type(), name)
    }

    pub(crate) fn get_element_ty(&self, container_ty: &Ty, index: usize) -> Ty {
        match container_ty {
            Ty::Array(elem_ty, _) => elem_ty.as_ref().clone(),
            Ty::Ref(inner_ty)
            | Ty::MutRef(inner_ty)
            | Ty::IdRef(inner_ty)
            | Ty::Borrow(inner_ty)
            | Ty::BorrowMut(inner_ty) => inner_ty.as_ref().clone(),
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

    pub(crate) fn get_fn(&self) -> FunctionValue<'ctx> {
        self.curr_fn.unwrap()
    }

    pub(crate) fn get_block(&mut self, idx: usize) -> BasicBlock<'ctx> {
        let fn_val = self.get_fn();
        if !self.blocks.contains_key(&idx) {
            let bb = self.lcx.append_basic_block(fn_val, &format!("B{}", idx));
            self.blocks.insert(idx, bb);
        }

        *self.blocks.get(&idx).unwrap()
    }

    pub(crate) fn get_local(&self, idx: usize) -> PointerValue<'ctx> {
        *self
            .locals
            .get(&idx)
            .expect(&format!("could not find variable: {}", idx))
    }

    pub(crate) fn load_local(&mut self, idx: usize) -> Result<BasicValueEnum<'ctx>, BuilderError> {
        let ptr = self.get_local(idx);
        self.load_pointer(ptr)
    }

    pub(crate) fn is_local_slot(&mut self, ptr: &PointerValue<'ctx>) -> bool {
        self.locals.values().any(|slot_ptr| ptr == slot_ptr)
    }

    pub(crate) fn load_pointer(
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

    pub(crate) fn get_element_ptr(
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
        } else if matches!(
            container_ty,
            Ty::Array(_, _)
                | Ty::Ref(_)
                | Ty::MutRef(_)
                | Ty::IdRef(_)
                | Ty::RawPtr(_)
                | Ty::Borrow(_)
                | Ty::BorrowMut(_)
        ) {
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

    pub(crate) fn byte_offset_ptr(
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

    pub(crate) fn get_local_llvm_ty(&mut self, idx: usize) -> BasicTypeEnum<'ctx> {
        let ptr = self.get_local(idx);
        let ty = self.get_pointee_ty(ptr).clone();
        self.to_llvm_type(&ty)
    }

    pub(crate) fn get_field_ptr(
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

    pub(crate) fn to_llvm_type(&mut self, ty: &Ty) -> BasicTypeEnum<'ctx> {
        match ty {
            Ty::Never => self.lcx.struct_type(&[], false).as_basic_type_enum(),
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
            Ty::Func(_, _)
            | Ty::Ref(_)
            | Ty::MutRef(_)
            | Ty::IdRef(_)
            | Ty::RawPtr(_)
            | Ty::Borrow(_)
            | Ty::BorrowMut(_) => self
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

                // Enum types lower to `{ i32, [N x i8] }`.
                if self.enum_defs.contains_key(fqn) {
                    return self.get_enum_llvm_type(fqn, args).as_basic_type_enum();
                }

                // For all other projections, lower to the underlying struct type.
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

    pub(crate) fn to_llvm_fn_ty(
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
        if ret_ty.is_unit() || ret_ty.is_never() {
            return self.lcx.void_type().fn_type(&param_tys, false);
        }

        let ret_ty = self.to_llvm_type(ret_ty);
        ret_ty.fn_type(&param_tys, false)
    }

    pub(crate) fn alloca(&mut self, ty: &Ty) -> Result<PointerValue<'ctx>, BuilderError> {
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

    pub(crate) fn maybe_load_pointer(
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
    pub(crate) fn marshal_arg_value(
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
                    Ty::Ref(_)
                    | Ty::MutRef(_)
                    | Ty::IdRef(_)
                    | Ty::RawPtr(_)
                    | Ty::Borrow(_)
                    | Ty::BorrowMut(_) => {
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
        if matches!(
            ray_param_ty,
            Ty::Ref(_) | Ty::MutRef(_) | Ty::IdRef(_) | Ty::Borrow(_) | Ty::BorrowMut(_)
        ) {
            panic!(
                "COMPILER BUG: Ray pointer parameter lowered to non-pointer LLVM parameter; ray_param_ty={} llvm_param_ty={}",
                ray_param_ty,
                expected.print_to_string().to_string()
            );
        }

        self.maybe_load_pointer(val)
    }

    pub(crate) fn store(
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
                Ty::Ref(_)
                | Ty::MutRef(_)
                | Ty::IdRef(_)
                | Ty::RawPtr(_)
                | Ty::Borrow(_)
                | Ty::BorrowMut(_) => {
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
    pub(crate) fn build_set_local(
        &mut self,
        idx: usize,
        value: &lir::Value,
        srcmap: &SourceMap,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        // Enum construction is handled in-place; intercept before the generic aggregate path.
        if let lir::Value::Enum(ev) = value {
            return self.build_enum_init(idx, ev, srcmap);
        }

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
    pub(crate) fn build_memcpy(
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
    pub(crate) fn memcpy_aggregate_from_value(
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

    /// Build a return for the current function, using Ray's return type to
    /// decide whether to return a pointer (aggregate) or a scalar value.
    /// For aggregates without sret, if the LLVM return is non-pointer we load once.
    pub(crate) fn build_typed_return(
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

    pub(crate) fn fn_attr(&self, fn_val: FunctionValue<'ctx>, key: &str, val: &str) {
        let attribute = self.lcx.create_string_attribute(key, val);
        fn_val.add_attribute(AttributeLoc::Function, attribute);
    }

    pub(crate) fn get_struct_type(&mut self, path: &ItemPath, args: &[Ty]) -> StructType<'ctx> {
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

    /// Returns the LLVM struct type for an enum: `{ i32, [N x i8] }` where N
    /// is the maximum payload size in bytes across all variants.
    pub(crate) fn get_enum_llvm_type(&mut self, path: &ItemPath, args: &[Ty]) -> StructType<'ctx> {
        let key = Ty::nominal(path.clone(), args.to_vec());

        if let Some(st) = self.struct_types.get(&key) {
            return st.clone();
        }

        let opaque = self.lcx.opaque_struct_type(&key.to_mangled());
        self.struct_types.insert(key.clone(), opaque);

        // Clone the enum definition and apply type argument substitution.
        let mut enum_ty = self
            .enum_defs
            .get(path)
            .cloned()
            .expect(&format!("enum type not found: {}", path));

        if !args.is_empty() {
            let vars = enum_ty.ty.vars.clone();
            assert_eq!(
                vars.len(),
                args.len(),
                "cannot instantiate enum type: path={} vars={} args={}",
                path,
                vars.len(),
                args.len()
            );
            let mut subst = Subst::new();
            for (var, arg) in vars.into_iter().zip(args.iter()) {
                subst.insert(var, arg.clone());
            }
            enum_ty.apply_subst(&subst);
        }

        // Compute maximum payload size in bytes across all variants.
        let mut max_payload_bytes: u64 = 0;
        for variant in &enum_ty.variants {
            let mut variant_bytes: u64 = 0;
            for field_scheme in &variant.field_types {
                let field_llvm_ty = self.to_llvm_type(field_scheme.mono());
                let td = self.target_machine.get_target_data();
                let align = td.get_preferred_alignment(&field_llvm_ty) as u64;
                let size = td.get_abi_size(&field_llvm_ty);
                variant_bytes = (variant_bytes + align - 1) & !(align - 1);
                variant_bytes += size;
            }
            max_payload_bytes = max_payload_bytes.max(variant_bytes);
        }

        // Body: { i32 tag, [N x i8] payload }
        let i32_ty = self.lcx.i32_type();
        let payload_ty = self.lcx.i8_type().array_type(max_payload_bytes as u32);
        let llvm_struct = self
            .struct_types
            .get(&key)
            .expect("enum not registered")
            .clone();
        llvm_struct.set_body(&[i32_ty.into(), payload_ty.into()], false);
        llvm_struct
    }

    /// Initialises the enum local at `idx` from an `EnumValue`: stores the tag
    /// into field 0 and packs payload fields into the byte-array field 1.
    pub(crate) fn build_enum_init(
        &mut self,
        idx: usize,
        ev: &lir::EnumValue,
        srcmap: &SourceMap,
    ) -> Result<InstructionValue<'ctx>, BuilderError> {
        let dst_ptr = self.get_local(idx);

        // Recover type args from the destination local's declared type so
        // generic enums are instantiated correctly.
        let args = match self.local_tys[idx].clone() {
            Ty::Proj(_, args) => args,
            _ => vec![],
        };
        let enum_llvm_ty = self.get_enum_llvm_type(&ev.path, &args);

        let zero = self.zero();
        let tag_field = self.ptr_type().const_int(0, false);
        let payload_field = self.ptr_type().const_int(1, false);

        // Store tag into struct field 0.
        let tag_ptr = unsafe {
            self.builder
                .build_gep(enum_llvm_ty, dst_ptr, &[zero, tag_field], "enum_tag_ptr")?
        };
        self.register_pointee_ty(tag_ptr, Ty::i32());
        let tag_val = self.lcx.i32_type().const_int(ev.tag as u64, false);
        let mut last_inst = self.builder.build_store(tag_ptr, tag_val)?;

        if ev.fields.is_empty() {
            return Ok(last_inst);
        }

        // Get pointer to the payload byte array (struct field 1).
        let payload_ptr = unsafe {
            self.builder.build_gep(
                enum_llvm_ty,
                dst_ptr,
                &[zero, payload_field],
                "enum_payload_ptr",
            )?
        };

        // Pack each payload field at the correct byte offset.
        let mut byte_offset: u64 = 0;
        for field_var in &ev.fields {
            let field_ty = self.type_of(field_var).clone();
            let field_llvm_ty = self.to_llvm_type(&field_ty);
            let td = self.target_machine.get_target_data();
            let align = td.get_preferred_alignment(&field_llvm_ty) as u64;
            let size = td.get_abi_size(&field_llvm_ty);

            // Advance to satisfy alignment.
            byte_offset = (byte_offset + align - 1) & !(align - 1);

            // GEP to the field's slot within the payload byte array.
            let field_ptr = if byte_offset == 0 {
                payload_ptr
            } else {
                let off_val = self.ptr_type().const_int(byte_offset, false);
                unsafe {
                    self.builder.build_gep(
                        self.lcx.i8_type(),
                        payload_ptr,
                        &[off_val],
                        "payload_field_ptr",
                    )?
                }
            };
            self.register_pointee_ty(field_ptr, field_ty.clone());

            if field_ty.is_aggregate() {
                let src_ptr = match field_var {
                    lir::Variable::Local(i) => self.get_local(*i),
                    other => {
                        panic!("aggregate enum payload field must be a local: {:?}", other)
                    }
                };
                let field_align = td.get_abi_alignment(&field_llvm_ty);
                let size_val = self.ptr_type().const_int(size, false);
                last_inst = self
                    .builder
                    .build_memcpy(field_ptr, field_align, src_ptr, field_align, size_val)?
                    .as_instruction_value()
                    .unwrap();
            } else {
                let field_val = match field_var {
                    lir::Variable::Local(i) => self.load_local(*i)?,
                    other => other.codegen(self, srcmap)?,
                };
                last_inst = self.builder.build_store(field_ptr, field_val)?;
            }

            byte_offset += size;
        }

        Ok(last_inst)
    }

    /// Creates a null-terminated constant byte array global and returns a pointer to it.
    pub(crate) fn create_cstring_global(&self, s: &str, name: &str) -> GlobalValue<'ctx> {
        let i8_ty = self.lcx.i8_type();
        let mut bytes: Vec<_> = s
            .bytes()
            .map(|b| i8_ty.const_int(b as u64, false))
            .collect();
        bytes.push(i8_ty.const_int(0, false)); // null terminator
        let array_val = i8_ty.const_array(&bytes);
        let global = self.module.add_global(
            i8_ty.array_type(bytes.len() as u32),
            Some(AddressSpace::default()),
            name,
        );
        global.set_initializer(&array_val);
        global.set_linkage(Linkage::Internal);
        global.set_constant(true);
        global
    }
}
