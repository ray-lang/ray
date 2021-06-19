use std::{
    collections::{BTreeMap, HashMap, HashSet},
    ops::Deref,
};

use itertools::Itertools;
use lir::{SymbolSet, Variable, LCA};

use crate::{
    ast::{Node, Path},
    lir,
    span::SourceMap,
    typing::{ty::Ty, TyCtx},
    utils::join,
};

pub mod wasm;

pub fn codegen(prog: &lir::Program, tcx: &TyCtx, srcmap: &SourceMap) -> wasm::Module {
    let mut ctx = CodegenCtx::new();
    prog.codegen(&mut ctx, tcx, srcmap);
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
    symbols: &mut SymbolSet,
    fn_map: &HashMap<Path, &Node<lir::Func>>,
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
    fn_index: HashMap<Path, (u32, Option<usize>)>,
    data_addrs: HashMap<usize, i32>,
    globals: HashMap<String, u32>,
    local_tys: Vec<Ty>,
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
            local_tys: vec![],
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

    fn type_of(&self, var: &lir::Variable) -> &Ty {
        match var {
            Variable::Unit => panic!("unit is untyped"),
            Variable::Data(_) => panic!("data is untyped"),
            Variable::Global(idx) => {
                todo!("type of global: {}", idx)
            }
            Variable::Local(idx) => &self.local_tys[*idx],
        }
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

    fn add_func_name(&mut self, idx: u32, name: &Path) {
        let name_sec = self.module.names_section_mut().unwrap();
        name_sec
            .functions_mut()
            .as_mut()
            .unwrap()
            .names_mut()
            .insert(idx, name.to_string());
    }

    fn add_func(&mut self, name: &Path, func: wasm::Func, body: wasm::FuncBody) -> u32 {
        let func_sec = self.module.function_section_mut().unwrap();
        func_sec.entries_mut().push(func);

        let code_sec = self.module.code_section_mut().unwrap();
        let body_idx = code_sec.bodies().len();
        code_sec.bodies_mut().push(body);

        let idx = self.fn_index.len() as u32;
        self.fn_index.insert(name.clone(), (idx, Some(body_idx)));

        self.add_func_name(idx, name);

        // TODO: don't add _every_ function to the exports
        let export_sec = self.module.export_section_mut().unwrap();
        export_sec.entries_mut().push(wasm::ExportEntry::new(
            name.to_string(),
            wasm::Internal::Function(idx),
        ));

        idx
    }

    fn add_func_import(&mut self, name: Path) {
        let idx = self.fn_index.len() as u32;
        self.fn_index.insert(name.clone(), (idx, None));
        self.add_func_name(idx, &name);
    }

    fn get_body(&mut self, name: &Path) -> &mut wasm::FuncBody {
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

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output;
}

impl<T> Codegen for Vec<T>
where
    T: Codegen<Output = Vec<wasm::Instruction>>,
{
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        self.iter()
            .flat_map(|t| t.codegen(ctx, tcx, srcmap))
            .collect()
    }
}

impl<T, I> Codegen for Node<T>
where
    T: Codegen<Output = I>,
{
    type Output = I;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        self.value.codegen(ctx, tcx, srcmap)
    }
}

impl Codegen for lir::Program {
    type Output = ();

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
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

                let import = wasm::ImportEntry::new(src, ext.name.to_string(), external);
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
            if srcmap.has_inline(f) || !symbols.contains(&f.name) {
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

            // add local for "local" heap pointer
            locals.push(wasm::Local::new(1, wasm::ValueType::I32));
            let body = wasm::FuncBody::new(locals, wasm::Instructions::new(vec![]));

            // add function to the section
            ctx.add_func(&f.name, func, body);

            funcs.push(f);
        }

        // then codegen!
        for f in funcs {
            let local_tys = f
                .locals
                .iter()
                .map(|loc| loc.ty.clone())
                .collect::<Vec<_>>();
            let body = ctx.get_body(&f.name);
            ctx.local_hp = Some((body.locals().len() - 1) as u32);
            ctx.local_tys = local_tys;
            f.codegen(ctx, tcx, srcmap);
        }
    }
}

impl Codegen for lir::Func {
    type Output = ();

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        fn new_codegen_block(
            func: &lir::Func,
            label: usize,
            depth: usize,
            stop_label: Option<usize>,
            blocks: &mut BTreeMap<usize, Vec<wasm::Instruction>>,
            loops: &HashMap<usize, lir::Loop>,
            curr_loop: Option<&lir::Loop>,
        ) -> Vec<wasm::Instruction> {
            if label >= func.blocks.len() {
                // we must've gone past the end
                return vec![];
            }

            log::debug!("depth: {}", depth);
            log::debug!("current label: {}", label);
            log::debug!("stop label: {:?}", stop_label);
            if matches!(stop_label, Some(stop_label) if stop_label == label) {
                return vec![];
            }

            let block = &func.blocks[label];
            let block_insts = match blocks.remove(&label) {
                Some(i) => i,
                // TODO: is this okay?
                _ => vec![], // already been codegen'd
            };

            let mut insts = vec![];

            // check the final control instruction to determine what to codegen next
            let mut next_label = if let Some(last) = block.last() {
                match last {
                    &lir::Inst::If(lir::If {
                        cond_loc,
                        then_label,
                        else_label,
                    }) => {
                        let mut curr_loop = curr_loop;
                        if loops.contains_key(&label) {
                            curr_loop = loops.get(&label);
                        }

                        let end_label = if block.is_loop_header() {
                            // determine the LCA using the common exit node of the loop
                            curr_loop.unwrap().common_exit
                        } else {
                            // determine the LCA for the then and else labels
                            func.cfg
                                .lowest_common_ancestor(
                                    then_label,
                                    else_label,
                                    &vec![then_label, else_label],
                                )
                                .unwrap()
                        };

                        log::debug!("end label: {}", end_label);

                        // detemine which block instructions are necessary
                        let mut depth = depth;
                        let mut local_depth = 0;
                        if block.is_loop_header() {
                            // a block that can targeted and a loop block
                            insts.push(wasm::Instruction::Block(wasm::BlockType::NoResult));
                            insts.push(wasm::Instruction::Loop(wasm::BlockType::NoResult));

                            // reset the block depth to 2 for the loop
                            depth = 2;
                            local_depth = 2;
                        } else if block.is_if_header() {
                            insts.push(wasm::Instruction::Block(wasm::BlockType::NoResult));
                            depth += 1;
                            local_depth += 1;

                            // if we're NOT in a loop OR the end label IS contained in the loop
                            if curr_loop.map_or(true, |l| l.nodes.contains(&end_label)) {
                                // add another block
                                log::debug!(
                                    "no current loop or it contains end label: {}",
                                    end_label
                                );
                                insts.push(wasm::Instruction::Block(wasm::BlockType::NoResult));
                                depth += 1;
                                local_depth += 1;
                            }
                        }

                        insts.extend(block_insts);
                        insts.push(wasm::Instruction::GetLocal(cond_loc as u32));
                        insts.push(wasm::Instruction::I32Eqz);

                        // loops break to the outer block
                        if block.is_loop_header() {
                            insts.push(wasm::Instruction::BrIf(1));
                        } else if block.is_if_header() {
                            // if/else breaks to the inner block (skipping the then block)
                            insts.push(wasm::Instruction::BrIf(0));
                        }

                        // generate the code for the two branches
                        let then_insts = new_codegen_block(
                            func,
                            then_label,
                            depth,
                            Some(end_label),
                            blocks,
                            loops,
                            curr_loop,
                        );
                        insts.extend(then_insts);

                        if curr_loop.is_none() && block.is_if_header() {
                            // if the last instruction was not a break, then break to the outer block
                            if !matches!(insts.last(), Some(wasm::Instruction::Br(_))) {
                                insts.push(wasm::Instruction::Br(1));
                            }
                        }

                        insts.push(wasm::Instruction::End);
                        local_depth -= 1;

                        if else_label != end_label {
                            let else_insts = new_codegen_block(
                                func,
                                else_label,
                                depth - 1,
                                Some(end_label),
                                blocks,
                                loops,
                                curr_loop,
                            );
                            insts.extend(else_insts);

                            if local_depth == 1 {
                                insts.push(wasm::Instruction::End);
                            }
                        } else {
                            insts.push(wasm::Instruction::End);
                        }

                        // then continue using the end label
                        Some(end_label)
                    }
                    lir::Inst::Break(_) => todo!("codegen Break"),
                    &lir::Inst::Goto(label) => {
                        insts.extend(block_insts);
                        Some(label)
                    }
                    lir::Inst::Halt | lir::Inst::Return(_) => {
                        insts.extend(block_insts);
                        None
                    }
                    i => panic!("COMPILER BUG: instruction is not a control {}", i),
                }
            } else {
                // ignore the empty block
                panic!(
                    "COMPILER BUG: block is empty in func {}: {}",
                    func.name, label
                )
            };

            // determine if we need to break in order to reach the next block
            let curr_label = label;
            if let (Some(curr_loop), Some(label)) = (curr_loop, next_label) {
                if !curr_loop.nodes.contains(&label) && curr_loop.is_exit_node(curr_label) {
                    // if the current loop does not contain the next label and the curr label
                    // is not the loop's exit node, break to the outer loop depth
                    log::debug!("current loop does not contain next label: {}", label);
                    log::debug!("break to depth: {}", depth - 1);
                    insts.push(wasm::Instruction::Br((depth - 1) as u32));
                } else if label == curr_loop.header() {
                    log::debug!("next label is loop header: {}", label);
                    log::debug!("break to depth: 0");
                    log::debug!("clear the next label");
                    next_label = None;
                    insts.push(wasm::Instruction::Br(0));
                }
            }

            if let Some(next_label) = next_label {
                insts.extend(new_codegen_block(
                    func, next_label, depth, stop_label, blocks, loops, curr_loop,
                ));
            }

            insts
        }

        log::debug!("codegen: {}", self);

        log::debug!(
            "cfg: {:?}",
            petgraph::dot::Dot::with_config(&self.cfg, &[petgraph::dot::Config::EdgeNoLabel])
        );

        // generate code for each block, storing them in the map
        let mut blocks = BTreeMap::new();
        for block in self.blocks.iter() {
            blocks.insert(block.label(), block.codegen(ctx, tcx, srcmap));
        }

        let loops = self.find_loops();

        let mut insts = new_codegen_block(self, 0, 0, None, &mut blocks, &loops, None);
        insts.push(wasm::Instruction::End);

        // add the instructions to the code body
        ctx.get_body(&self.name)
            .code_mut()
            .elements_mut()
            .extend(insts);
    }
}

impl Codegen for lir::Block {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        self.deref().codegen(ctx, tcx, srcmap)
    }
}

impl Codegen for lir::Inst {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        match self {
            lir::Inst::Free(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Call(call) => call.codegen(ctx, tcx, srcmap),
            lir::Inst::CExternCall(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetGlobal(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::SetLocal(idx, v) => {
                let mut inst = v.codegen(ctx, tcx, srcmap);
                inst.push(wasm::Instruction::SetLocal(*idx as u32));
                inst
            }
            lir::Inst::MemCopy(dst, src, size) => {
                let mut inst = dst.codegen(ctx, tcx, srcmap);
                inst.extend(src.codegen(ctx, tcx, srcmap));
                inst.extend(size.codegen(ctx, tcx, srcmap));
                inst.push(wasm::Instruction::Bulk(wasm::BulkInstruction::MemoryCopy));
                inst
            }
            lir::Inst::Store(s) => s.codegen(ctx, tcx, srcmap),
            lir::Inst::IncRef(_, _) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::DecRef(_) => todo!("codegen lir::Inst: {}", self),
            lir::Inst::Return(v) => {
                let mut inst = v.codegen(ctx, tcx, srcmap);
                inst.push(wasm::Instruction::Return);
                inst
            }
            // skip all of the control instructions (expect return), which will be processed later
            lir::Inst::Goto(_) | lir::Inst::Break(_) | lir::Inst::If(_) | lir::Inst::Halt => vec![],
        }
    }
}

impl Codegen for lir::Value {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        match self {
            lir::Value::VarRef(_) => {
                unreachable!("COMPILER BUG: this should be removed by this point")
            }
            lir::Value::Empty => vec![],
            lir::Value::Atom(a) => a.codegen(ctx, tcx, srcmap),
            lir::Value::Malloc(m) => m.codegen(ctx, tcx, srcmap),
            lir::Value::Call(c) => c.codegen(ctx, tcx, srcmap),
            lir::Value::CExternCall(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::Select(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::Phi(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::Load(l) => l.codegen(ctx, tcx, srcmap),
            lir::Value::Lea(_) => todo!("codegen lir::Value: {}", self),
            lir::Value::GetField(g) => g.codegen(ctx, tcx, srcmap),
            lir::Value::BasicOp(b) => b.codegen(ctx, tcx, srcmap),
            lir::Value::IntConvert(_) => todo!("codegen lir::Value: {}", self),
        }
    }
}

impl Codegen for lir::Malloc {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        let lir::Malloc(size) = self;
        let idx = ctx.global("heap_ptr");
        let mut inst = vec![
            wasm::Instruction::GetGlobal(idx),
            wasm::Instruction::TeeLocal(ctx.local_hp.unwrap()),
            // make sure the pointer is 4-byte aligned
            // aligned = (offset + 3) & -4
            wasm::Instruction::I32Const(3),
            wasm::Instruction::I32Add,
            wasm::Instruction::I32Const(-4),
            wasm::Instruction::I32And,
            wasm::Instruction::TeeLocal(ctx.local_hp.unwrap()),
        ];

        if let lir::Atom::Size(s) = size {
            let bytes = size_to_bytes(s) as i32;
            inst.push(wasm::Instruction::I32Const(bytes));
        } else {
            inst.extend(size.codegen(ctx, tcx, srcmap));
        }
        inst.extend(vec![
            wasm::Instruction::I32Add,
            wasm::Instruction::SetGlobal(idx),
        ]);

        inst.push(wasm::Instruction::GetLocal(ctx.local_hp.unwrap()));
        inst
    }
}

impl Codegen for lir::Load {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        let size = size_to_bytes(&self.size);
        let offset = size_to_bytes(&self.offset) as u32;
        let mut inst = self.src.codegen(ctx, tcx, srcmap);
        inst.push(match size {
            1 => wasm::Instruction::I32Load8U(0, offset),
            2 => wasm::Instruction::I32Load16U(0, offset),
            4 => wasm::Instruction::I32Load(0, offset),
            8 => wasm::Instruction::I64Load(0, offset),
            _ => unreachable!("invalid load size: {}", size),
        });
        inst
    }
}

impl Codegen for lir::Store {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        let size = size_to_bytes(&self.size);
        let offset = size_to_bytes(&self.offset) as u32;
        let mut insts = self.dst.codegen(ctx, tcx, srcmap);
        insts.extend(self.value.codegen(ctx, tcx, srcmap));

        let op = match size {
            1 => wasm::Instruction::I32Store8(0, offset),
            2 => wasm::Instruction::I32Store16(0, offset),
            4 => wasm::Instruction::I32Store(0, offset),
            8 => wasm::Instruction::I64Store(0, offset),
            _ => unreachable!("invalid store size: {}", size),
        };
        insts.push(op);
        insts
    }
}

impl Codegen for lir::If {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, _: &mut CodegenCtx, _: &TyCtx, _: &SourceMap) -> Self::Output {
        vec![]
    }
}

impl Codegen for lir::Break {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, _: &mut CodegenCtx, _: &TyCtx, _: &SourceMap) -> Self::Output {
        unimplemented!("lir::Break::codegen")
    }
}

impl Codegen for lir::GetField {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        // get the field offset and size
        let lhs_ty = ctx.type_of(&self.src);
        let lhs_fqn = lhs_ty.get_path().unwrap();
        let lhs_ty = tcx.get_struct_ty(&lhs_fqn).unwrap();
        let mut offset = lir::Size::zero();
        let mut size = lir::Size::zero();
        for (name, field_ty) in lhs_ty.fields.iter() {
            size = field_ty.size_of();
            if name == &self.field {
                break;
            }
            offset += size;
        }

        let size = size_to_bytes(&size);
        let offset = size_to_bytes(&offset) as u32;
        let mut inst = self.src.codegen(ctx, tcx, srcmap);
        inst.push(match size {
            1 => wasm::Instruction::I32Load8U(0, offset),
            2 => wasm::Instruction::I32Load16U(0, offset),
            4 => wasm::Instruction::I32Load(0, offset),
            8 => wasm::Instruction::I64Load(0, offset),
            _ => unreachable!("invalid load size: {}", size),
        });
        inst
    }
}

impl Codegen for lir::Call {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        let mut insts = self.args.codegen(ctx, tcx, srcmap);
        let (idx, _) = ctx.fn_index.get(&self.fn_name).expect(
            format!(
                "cannot find function `{}` in index: {:#?}",
                self.fn_name,
                ctx.fn_index.keys()
            )
            .as_str(),
        );
        insts.push(wasm::Instruction::Call(*idx));
        insts
    }
}

impl Codegen for lir::BasicOp {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
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
        insts.extend(self.operands.codegen(ctx, tcx, srcmap));
        insts.push(op);
        insts
    }
}

impl Codegen for lir::Atom {
    type Output = Vec<wasm::Instruction>;

    fn codegen(&self, ctx: &mut CodegenCtx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        match self {
            lir::Atom::Variable(v) => v.codegen(ctx, tcx, srcmap),
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

    fn codegen(&self, ctx: &mut CodegenCtx, _: &TyCtx, _: &SourceMap) -> Self::Output {
        match self {
            lir::Variable::Data(i) => {
                let addr = ctx.data_addrs.get(i).unwrap();
                vec![wasm::Instruction::I32Const(*addr)]
            }
            lir::Variable::Global(i) => vec![wasm::Instruction::GetGlobal(*i as u32)],
            lir::Variable::Local(i) => vec![wasm::Instruction::GetLocal(*i as u32)],
            lir::Variable::Unit => vec![],
        }
    }
}
