use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::{
    ast::{Node, SourceInfo},
    lir,
    typing::ty::Ty,
    utils::join,
};

pub mod wasm;

pub fn codegen(prog: &lir::Program) -> wasm::Module {
    let mut ctx = CodegenCtx::new();
    prog.codegen(&mut ctx);
    ctx.module
}

fn size_to_bytes(s: &lir::Size) -> usize {
    (s.ptrs * 4) + s.bytes
}

fn i32_expr(value: i32) -> wasm::InitExpr {
    wasm::InitExpr::new(vec![
        wasm::Instruction::I32Const(value),
        wasm::Instruction::End,
    ])
}

fn collect_symbols(
    func: &lir::Func,
    symbols: &mut HashSet<String>,
    fn_map: &HashMap<String, &lir::Func>,
) {
    for sym in func.symbols.iter() {
        if !symbols.contains(sym) {
            symbols.insert(sym.clone());
            if let Some(func) = fn_map.get(sym) {
                collect_symbols(func, symbols, fn_map)
            }
        }
    }
}

struct CodegenCtx {
    module: wasm::Module,
    fn_types: HashMap<String, u32>,
    fn_index: HashMap<String, (u32, Option<usize>)>,
    data_addrs: HashMap<usize, i32>,
    globals: HashMap<String, u32>,
    local_hp: Option<u32>,
}

impl CodegenCtx {
    fn new() -> CodegenCtx {
        CodegenCtx {
            module: wasm::Module::new(vec![]),
            fn_types: HashMap::new(),
            fn_index: HashMap::new(),
            data_addrs: HashMap::new(),
            globals: HashMap::new(),
            local_hp: None,
        }
    }

    fn global(&mut self, name: &str) -> u32 {
        let name = name.to_string();
        if let Some(idx) = self.globals.get(&name) {
            *idx
        } else {
            let idx = self.globals.len() as u32;
            self.globals.insert(name, idx);
            idx
        }
    }

    fn add_global(
        &mut self,
        name: String,
        init_value: i32,
        ty: wasm::ValueType,
        is_mutable: bool,
    ) -> u32 {
        let idx = self.globals.len() as u32;
        self.globals.insert(name, idx);
        let entries = self.module.global_section_mut().unwrap().entries_mut();
        entries.push(wasm::GlobalEntry::new(
            wasm::GlobalType::new(ty, is_mutable),
            i32_expr(init_value),
        ));
        idx
    }

    fn get_type_ref(&mut self, param_tys: &Vec<Ty>, ret_ty: &Ty) -> u32 {
        let key = format!("({}):{}", join(param_tys, ","), ret_ty);
        if let Some(&type_ref) = self.fn_types.get(&key) {
            type_ref
        } else {
            // add type to the module
            let ty = wasm::to_fn_ty(param_tys, ret_ty);
            let type_ref = if let Some(sec) = self.module.type_section_mut() {
                let r = sec.types().len() as u32;
                sec.types_mut().push(ty);
                r
            } else {
                let sec = wasm::Section::Type(wasm::TypeSection::with_types(vec![ty]));
                self.module.insert_section(sec).unwrap();
                0
            };

            self.fn_types.insert(key, type_ref);
            type_ref
        }
    }

    fn add_func_name(&mut self, idx: u32, name: String) {
        let name_sec = self.module.names_section_mut().unwrap();
        name_sec
            .functions_mut()
            .as_mut()
            .unwrap()
            .names_mut()
            .insert(idx, name.clone());
    }

    fn add_func(&mut self, name: String, func: wasm::Func, body: wasm::FuncBody) -> u32 {
        let func_sec = self.module.function_section_mut().unwrap();
        func_sec.entries_mut().push(func);

        let code_sec = self.module.code_section_mut().unwrap();
        let body_idx = code_sec.bodies().len();
        code_sec.bodies_mut().push(body);

        let idx = self.fn_index.len() as u32;
        self.fn_index.insert(name.clone(), (idx, Some(body_idx)));

        self.add_func_name(idx, name.clone());

        // TODO: don't add _every_ function to the exports
        let export_sec = self.module.export_section_mut().unwrap();
        export_sec
            .entries_mut()
            .push(wasm::ExportEntry::new(name, wasm::Internal::Function(idx)));

        idx
    }

    fn add_func_import(&mut self, name: String) {
        let idx = self.fn_index.len() as u32;
        self.fn_index.insert(name.clone(), (idx, None));
        self.add_func_name(idx, name);
    }

    fn get_body(&mut self, name: &String) -> &mut wasm::FuncBody {
        let (_, body_idx) = self.fn_index.get(name).unwrap();
        let body_idx = body_idx.unwrap();
        self.module
            .code_section_mut()
            .unwrap()
            .bodies_mut()
            .get_mut(body_idx)
            .expect(format!("could not find function body: {}", name).as_str())
    }
}

trait Simplify {
    fn simplify(self) -> Self;
}

impl Simplify for Vec<wasm::Instruction> {
    fn simplify(self) -> Self {
        self.into_iter()
            .coalesce(|x, y| match (&x, &y) {
                (wasm::Instruction::SetLocal(i), wasm::Instruction::GetLocal(j)) if i == j => {
                    Ok(wasm::Instruction::TeeLocal(*i))
                }
                _ => Err((x, y)),
            })
            .collect()
    }
}

trait GetLocals {
    fn get_locals(&self) -> HashSet<u32>;
}

impl GetLocals for Vec<wasm::Instruction> {
    fn get_locals(&self) -> HashSet<u32> {
        let mut set = HashSet::new();
        for i in self {
            match i {
                wasm::Instruction::GetLocal(l)
                | wasm::Instruction::SetLocal(l)
                | wasm::Instruction::TeeLocal(l) => {
                    set.insert(*l);
                }
                _ => continue,
            }
        }
        set
    }
}

trait Codegen {
    type Output;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output;
}

impl<T> Codegen for Vec<T>
where
    T: Codegen<Output = Vec<wasm::Instruction>>,
{
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        self.iter().flat_map(|t| t.codegen(ctx)).collect()
    }
}

impl<T, I> Codegen for Node<T, SourceInfo>
where
    T: Codegen<Output = I>,
{
    type Output = I;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        self.value.codegen(ctx)
    }
}

impl Codegen for lir::Program {
    type Output = ();

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        // collect the function symbols
        let fn_map = self
            .funcs
            .iter()
            .map(|f| (f.name.clone(), f))
            .collect::<HashMap<_, _>>();

        let mut symbols = HashSet::new();
        let start_fn = &self.funcs[self.start_idx as usize];
        symbols.insert(start_fn.name.clone());
        collect_symbols(start_fn, &mut symbols, &fn_map);
        log::debug!("all symbols: {:?}", symbols);

        if self.funcs.len() != 0 || self.data.len() != 0 {
            // add export section
            let sec = wasm::Section::Export(wasm::ExportSection::with_entries(vec![]));
            ctx.module.insert_section(sec).unwrap();
        }

        if self.externs.len() != 0 || self.funcs.len() != 0 {
            // add a name section
            let sec = wasm::Section::Name(wasm::NameSection::new(
                None,
                Some(wasm::FunctionNameSubsection::default()),
                None,
            ));
            ctx.module.insert_section(sec).unwrap();
        }

        if self.externs.len() != 0 {
            let mut entries = vec![];
            for ext in self.externs.iter() {
                if !symbols.contains(&ext.name) {
                    continue;
                }

                let external = if let Ok((_, _, param_tys, ret_ty)) = ext.ty.try_borrow_fn() {
                    let ty_idx = ctx.get_type_ref(param_tys, ret_ty);
                    ctx.add_func_import(ext.name.clone());
                    wasm::External::Function(ty_idx)
                } else {
                    let content_type = wasm::to_wasm_ty(&ext.ty);
                    wasm::External::Global(wasm::GlobalType::new(content_type, ext.is_mutable))
                };

                let src = if let Some(src) = &ext.src {
                    src.clone()
                } else {
                    str!("env")
                };

                let import = wasm::ImportEntry::new(src, ext.name.clone(), external);
                entries.push(import);
            }

            if entries.len() != 0 {
                let sec = wasm::Section::Import(wasm::ImportSection::with_entries(entries));
                ctx.module.insert_section(sec).unwrap();
            }
        }

        if self.funcs.len() != 0 {
            // add a function section
            let sec = wasm::Section::Function(wasm::FunctionSection::with_entries(vec![]));
            ctx.module.insert_section(sec).unwrap();

            // add a code section
            let sec = wasm::Section::Code(wasm::CodeSection::with_bodies(vec![]));
            ctx.module.insert_section(sec).unwrap();
        }

        let data_end = if self.data.len() != 0 {
            // add the memory section
            let sec = wasm::Section::Memory(wasm::MemorySection::with_entries(vec![
                wasm::MemoryType::new(1, None),
            ]));
            ctx.module.insert_section(sec).unwrap();

            // export memory
            let export_sec = ctx.module.export_section_mut().unwrap();
            export_sec.entries_mut().push(wasm::ExportEntry::new(
                str!("memory"),
                wasm::Internal::Memory(0),
            ));

            // add data entries
            let mut entries = vec![];
            let mut offset = 0;
            for d in self.data.iter() {
                let value = d.value();
                let len = value.len() as i32;
                let idx = entries.len();

                // there is only one memory so index is always 0
                entries.push(wasm::DataSegment::new(0, Some(i32_expr(offset)), value));

                ctx.data_addrs.insert(idx, offset);
                offset += len;

                // make sure the offset is a multiple of 4
                if offset % 4 != 0 {
                    offset += 4 - (offset % 4);
                }
            }

            let sec = wasm::Section::Data(wasm::DataSection::with_entries(entries));
            ctx.module.insert_section(sec).unwrap();

            offset
        } else {
            0
        };

        // add the `heap` global
        let sec = wasm::Section::Global(wasm::GlobalSection::with_entries(vec![]));
        ctx.module.insert_section(sec).unwrap();
        ctx.add_global(str!("heap_ptr"), data_end, wasm::ValueType::I32, true);

        // first add each function
        let mut funcs = vec![];
        for f in self.funcs.iter() {
            if f.has_inline() || !symbols.contains(&f.name) {
                // don't generate inline functions or functions that are not in the symbol set
                continue;
            }

            let (_, _, param_tys, ret_ty) = f.ty.try_borrow_fn().unwrap();

            // create the function
            let func = wasm::Func::new(ctx.get_type_ref(param_tys, ret_ty));

            let mut locals = vec![];
            for loc in f.locals.iter() {
                let value_type = wasm::to_wasm_ty(&loc.ty);
                locals.push(wasm::Local::new(1, value_type));
            }

            // add local for "local" stack pointer
            locals.push(wasm::Local::new(1, wasm::ValueType::I32));
            let body = wasm::FuncBody::new(locals, wasm::Instructions::new(vec![]));

            // add function to the section
            ctx.add_func(f.name.clone(), func, body);

            funcs.push(f);
        }

        // then codegen!
        for f in funcs.iter() {
            let body = ctx.get_body(&f.name);
            ctx.local_hp = Some((body.locals().len() - 1) as u32);
            f.codegen(ctx);
        }
    }
}

impl Codegen for lir::Func {
    type Output = ();

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        // generate the instructions for the body of the function
        let mut inst = self.body.codegen(ctx).simplify();
        inst.push(wasm::Instruction::End);

        let body = ctx.get_body(&self.name);

        // find the locals that are unused and remove them
        let used_locals = inst.get_locals();
        let locals = body.locals_mut();
        let mut i = 0;
        let mut loc = 0;
        while i < locals.len() {
            if !used_locals.contains(&loc) {
                locals.remove(i);
            } else {
                i += 1;
            }
            loc += 1;
        }

        // add the instructions to the code body
        body.code_mut().elements_mut().extend(inst);
    }
}

impl Codegen for lir::Block {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        self.instructions.codegen(ctx)
    }
}

impl Codegen for lir::Inst {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        match self {
            lir::Inst::Value(v) => v.codegen(ctx),
            lir::Inst::Free(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetGlobal(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetLocal(idx, v) => {
                let mut inst = v.codegen(ctx);
                inst.push(wasm::Instruction::SetLocal(*idx as u32));
                inst
            }
            lir::Inst::Block(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Func(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::IfBlock(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Loop(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::MemCopy(dst, src, size) => {
                let mut inst = dst.codegen(ctx);
                inst.extend(src.codegen(ctx));
                inst.extend(size.codegen(ctx));
                inst.push(wasm::Instruction::Bulk(wasm::BulkInstruction::MemoryCopy));
                inst
            }
            lir::Inst::Store(s) => s.codegen(ctx),
            lir::Inst::IncRef(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::DecRef(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Return(v) => {
                let mut inst = v.codegen(ctx);
                inst.push(wasm::Instruction::Return);
                inst
            }
            lir::Inst::Break => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Halt => todo!("codegen lir::Inst: {}", self),
        }
    }
}

impl Codegen for lir::Value {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        match self {
            lir::Value::Empty => vec![],
            lir::Value::Atom(a) => a.codegen(ctx),
            lir::Value::Malloc(m) => m.codegen(ctx),
            lir::Value::Call(c) => c.codegen(ctx),
            lir::Value::CExternCall(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::Branch(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::Select(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::Load(l) => l.codegen(ctx),
            lir::Value::Lea(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::BasicOp(b) => b.codegen(ctx),
            lir::Value::IntConvert(_) => todo!("codegen lir::Value: {}", self),
        }
    }
}

impl Codegen for lir::Malloc {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        let lir::Malloc(size) = self;
        let idx = ctx.global("heap_ptr");
        let mut inst = vec![
            wasm::Instruction::GetGlobal(idx),
            wasm::Instruction::TeeLocal(ctx.local_hp.unwrap()),
        ];

        if let lir::Atom::Size(s) = size {
            // make sure that the global is a multiple of 4
            let mut bytes = size_to_bytes(s) as i32;
            if (bytes % 4) != 0 {
                bytes += 4 - (bytes % 4);
            }
            inst.push(wasm::Instruction::I32Const(bytes));
        } else {
            inst.extend(size.codegen(ctx));
        }
        inst.extend(vec![
            wasm::Instruction::I32Add,
            wasm::Instruction::SetGlobal(idx),
        ]);

        if !matches!(size, lir::Atom::Size(s)) {
            // if the size isn't a constant, then
            // make sure that the global is a multiple of 4
            inst.extend(vec![
                wasm::Instruction::GetGlobal(idx),
                wasm::Instruction::I32Const(4),
                wasm::Instruction::GetGlobal(idx),
                wasm::Instruction::I32Const(4),
                wasm::Instruction::I32RemU,
                wasm::Instruction::I32Sub,
                wasm::Instruction::I32Add,
                wasm::Instruction::SetGlobal(idx),
            ]);
        }

        inst.push(wasm::Instruction::GetLocal(ctx.local_hp.unwrap()));
        inst
    }
}

impl Codegen for lir::Load {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        let size = size_to_bytes(&self.size);
        let offset = size_to_bytes(&self.offset) as u32;
        let mut inst = self.src.codegen(ctx);
        inst.push(match size {
            1 => wasm::Instruction::I32Load8U(0, offset),
            2 => wasm::Instruction::I32Load16U(1, offset),
            4 => wasm::Instruction::I32Load(2, offset),
            8 => wasm::Instruction::I64Load(3, offset),
            _ => unreachable!("invalid load size: {}", size),
        });
        inst
    }
}

impl Codegen for lir::Store {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        let size = size_to_bytes(&self.size);
        let offset = size_to_bytes(&self.offset) as u32;
        let mut insts = self.dst.codegen(ctx);
        insts.extend(self.value.codegen(ctx));

        let op = match size {
            1 => wasm::Instruction::I32Store8(0, offset),
            2 => wasm::Instruction::I32Store16(1, offset),
            4 => wasm::Instruction::I32Store(2, offset),
            8 => wasm::Instruction::I64Store(3, offset),
            _ => unreachable!("invalid store size: {}", size),
        };
        insts.push(op);
        insts
    }
}

impl Codegen for lir::Call {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        let mut insts = self.args.codegen(ctx);
        let (idx, _) = ctx
            .fn_index
            .get(&self.fn_name)
            .expect(format!("cannot find function {}", self.fn_name).as_str());
        insts.push(wasm::Instruction::Call(*idx));
        insts
    }
}

impl Codegen for lir::BasicOp {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        // convert the lir op and size into a wasm op
        let op = match (self.op, self.size, self.signed) {
            // int sizes: ptrsize, 8, 16, 32
            (lir::Op::Eq, lir::Size { ptrs: 1, .. }, _)
            | (lir::Op::Eq, lir::Size { bytes: 1, .. }, _)
            | (lir::Op::Eq, lir::Size { bytes: 2, .. }, _)
            | (lir::Op::Eq, lir::Size { bytes: 4, .. }, _) => wasm::Instruction::I32Eq,
            (lir::Op::Neq, lir::Size { ptrs: 1, .. }, _)
            | (lir::Op::Neq, lir::Size { bytes: 1, .. }, _)
            | (lir::Op::Neq, lir::Size { bytes: 2, .. }, _)
            | (lir::Op::Neq, lir::Size { bytes: 4, .. }, _) => wasm::Instruction::I32Ne,
            (lir::Op::Add, lir::Size { ptrs: 1, .. }, _)
            | (lir::Op::Add, lir::Size { bytes: 1, .. }, _)
            | (lir::Op::Add, lir::Size { bytes: 2, .. }, _)
            | (lir::Op::Add, lir::Size { bytes: 4, .. }, _) => wasm::Instruction::I32Add,
            (lir::Op::Sub, lir::Size { ptrs: 1, .. }, _)
            | (lir::Op::Sub, lir::Size { bytes: 1, .. }, _)
            | (lir::Op::Sub, lir::Size { bytes: 2, .. }, _)
            | (lir::Op::Sub, lir::Size { bytes: 4, .. }, _) => wasm::Instruction::I32Sub,
            (lir::Op::Mul, lir::Size { ptrs: 1, .. }, _)
            | (lir::Op::Mul, lir::Size { bytes: 1, .. }, _)
            | (lir::Op::Mul, lir::Size { bytes: 2, .. }, _)
            | (lir::Op::Mul, lir::Size { bytes: 4, .. }, _) => wasm::Instruction::I32Mul,
            (lir::Op::Div, lir::Size { ptrs: 1, .. }, true)
            | (lir::Op::Div, lir::Size { bytes: 1, .. }, true)
            | (lir::Op::Div, lir::Size { bytes: 2, .. }, true)
            | (lir::Op::Div, lir::Size { bytes: 4, .. }, true) => wasm::Instruction::I32DivS,
            (lir::Op::Div, lir::Size { ptrs: 1, .. }, false)
            | (lir::Op::Div, lir::Size { bytes: 1, .. }, false)
            | (lir::Op::Div, lir::Size { bytes: 2, .. }, false)
            | (lir::Op::Div, lir::Size { bytes: 4, .. }, false) => wasm::Instruction::I32DivU,
            (lir::Op::Mod, lir::Size { ptrs: 1, .. }, true)
            | (lir::Op::Mod, lir::Size { bytes: 1, .. }, true)
            | (lir::Op::Mod, lir::Size { bytes: 2, .. }, true)
            | (lir::Op::Mod, lir::Size { bytes: 4, .. }, true) => wasm::Instruction::I32RemS,
            (lir::Op::Mod, lir::Size { ptrs: 1, .. }, false)
            | (lir::Op::Mod, lir::Size { bytes: 1, .. }, false)
            | (lir::Op::Mod, lir::Size { bytes: 2, .. }, false)
            | (lir::Op::Mod, lir::Size { bytes: 4, .. }, false) => wasm::Instruction::I32RemU,
            (lir::Op::Lt, lir::Size { ptrs: 1, .. }, true)
            | (lir::Op::Lt, lir::Size { bytes: 1, .. }, true)
            | (lir::Op::Lt, lir::Size { bytes: 2, .. }, true)
            | (lir::Op::Lt, lir::Size { bytes: 4, .. }, true) => wasm::Instruction::I32LtS,
            (lir::Op::Lt, lir::Size { ptrs: 1, .. }, false)
            | (lir::Op::Lt, lir::Size { bytes: 1, .. }, false)
            | (lir::Op::Lt, lir::Size { bytes: 2, .. }, false)
            | (lir::Op::Lt, lir::Size { bytes: 4, .. }, false) => wasm::Instruction::I32LtU,
            (lir::Op::Gt, lir::Size { ptrs: 1, .. }, true)
            | (lir::Op::Gt, lir::Size { bytes: 1, .. }, true)
            | (lir::Op::Gt, lir::Size { bytes: 2, .. }, true)
            | (lir::Op::Gt, lir::Size { bytes: 4, .. }, true) => wasm::Instruction::I32GtS,
            (lir::Op::Gt, lir::Size { ptrs: 1, .. }, false)
            | (lir::Op::Gt, lir::Size { bytes: 1, .. }, false)
            | (lir::Op::Gt, lir::Size { bytes: 2, .. }, false)
            | (lir::Op::Gt, lir::Size { bytes: 4, .. }, false) => wasm::Instruction::I32GtU,
            (lir::Op::LtEq, lir::Size { ptrs: 1, .. }, true)
            | (lir::Op::LtEq, lir::Size { bytes: 1, .. }, true)
            | (lir::Op::LtEq, lir::Size { bytes: 2, .. }, true)
            | (lir::Op::LtEq, lir::Size { bytes: 4, .. }, true) => wasm::Instruction::I32LeS,
            (lir::Op::LtEq, lir::Size { ptrs: 1, .. }, false)
            | (lir::Op::LtEq, lir::Size { bytes: 1, .. }, false)
            | (lir::Op::LtEq, lir::Size { bytes: 2, .. }, false)
            | (lir::Op::LtEq, lir::Size { bytes: 4, .. }, false) => wasm::Instruction::I32LeU,
            (lir::Op::GtEq, lir::Size { ptrs: 1, .. }, true)
            | (lir::Op::GtEq, lir::Size { bytes: 1, .. }, true)
            | (lir::Op::GtEq, lir::Size { bytes: 2, .. }, true)
            | (lir::Op::GtEq, lir::Size { bytes: 4, .. }, true) => wasm::Instruction::I32GeS,
            (lir::Op::GtEq, lir::Size { ptrs: 1, .. }, false)
            | (lir::Op::GtEq, lir::Size { bytes: 1, .. }, false)
            | (lir::Op::GtEq, lir::Size { bytes: 2, .. }, false)
            | (lir::Op::GtEq, lir::Size { bytes: 4, .. }, false) => wasm::Instruction::I32GeU,
            // int size: 64
            (lir::Op::Eq, lir::Size { bytes: 8, .. }, _) => wasm::Instruction::I64Eq,
            (lir::Op::Neq, lir::Size { bytes: 8, .. }, _) => wasm::Instruction::I64Ne,
            (lir::Op::Add, lir::Size { bytes: 8, .. }, _) => wasm::Instruction::I64Add,
            (lir::Op::Sub, lir::Size { bytes: 8, .. }, _) => wasm::Instruction::I64Sub,
            (lir::Op::Mul, lir::Size { bytes: 8, .. }, _) => wasm::Instruction::I64Mul,
            (lir::Op::Div, lir::Size { bytes: 8, .. }, true) => wasm::Instruction::I64DivS,
            (lir::Op::Div, lir::Size { bytes: 8, .. }, false) => wasm::Instruction::I64DivU,
            (lir::Op::Mod, lir::Size { bytes: 8, .. }, true) => wasm::Instruction::I64RemS,
            (lir::Op::Mod, lir::Size { bytes: 8, .. }, false) => wasm::Instruction::I64RemU,
            (lir::Op::Lt, lir::Size { bytes: 8, .. }, true) => wasm::Instruction::I64LtS,
            (lir::Op::Lt, lir::Size { bytes: 8, .. }, false) => wasm::Instruction::I64LtU,
            (lir::Op::Gt, lir::Size { bytes: 8, .. }, true) => wasm::Instruction::I64GtS,
            (lir::Op::Gt, lir::Size { bytes: 8, .. }, false) => wasm::Instruction::I64GtU,
            (lir::Op::LtEq, lir::Size { bytes: 8, .. }, true) => wasm::Instruction::I64LeS,
            (lir::Op::LtEq, lir::Size { bytes: 8, .. }, false) => wasm::Instruction::I64LeU,
            (lir::Op::GtEq, lir::Size { bytes: 8, .. }, true) => wasm::Instruction::I64GeS,
            (lir::Op::GtEq, lir::Size { bytes: 8, .. }, false) => wasm::Instruction::I64GeU,
            _ => todo!("binop: ({}, {}, {})", self.op, self.size, self.signed),
        };

        let mut insts = vec![];
        insts.extend(self.operands.codegen(ctx));
        insts.push(op);
        insts
    }
}

impl Codegen for lir::Atom {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        match self {
            lir::Atom::Variable(v) => v.codegen(ctx),
            lir::Atom::FuncRef(_) => todo!("codegen lir::Atom: {}", self),
            lir::Atom::Size(s) => {
                let bytes = size_to_bytes(s);
                vec![wasm::Instruction::I32Const(bytes as i32)]
            }
            lir::Atom::UintConst(c, size) => {
                let bytes = size_to_bytes(size);
                vec![if bytes > 4 {
                    wasm::Instruction::I64Const((*c) as i64)
                } else {
                    wasm::Instruction::I32Const((*c) as i32)
                }]
            }
            lir::Atom::IntConst(c, size) => {
                let bytes = size_to_bytes(size);
                vec![if bytes > 4 {
                    wasm::Instruction::I64Const(*c)
                } else {
                    wasm::Instruction::I32Const((*c) as i32)
                }]
            }
            lir::Atom::FloatConst(_, _) => todo!("codegen lir::Atom: {}", self),
            lir::Atom::RawString(_) => todo!("codegen lir::Atom: {}", self),
            lir::Atom::NilConst => vec![wasm::Instruction::I32Const(0)],
        }
    }
}

impl Codegen for lir::Variable {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx) -> Self::Output {
        match self {
            lir::Variable::Data(i) => {
                let addr = ctx.data_addrs.get(i).unwrap();
                vec![wasm::Instruction::I32Const(*addr)]
            }
            lir::Variable::Global(i) => vec![wasm::Instruction::GetGlobal(*i as u32)],
            lir::Variable::Local(i) => vec![wasm::Instruction::GetLocal(*i as u32)],
        }
    }
}
