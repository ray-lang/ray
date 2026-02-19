use std::collections::{HashMap, HashSet};

use ray_shared::pathlib::Path;

use crate::{
    Atom, Block, CExternCall, Call, Closure, Func, Global, Inst, Program, Select, Value, Variable,
};

/// Accumulated references to data and global segments found during tree-shaking.
pub struct RefCollector {
    pub data_refs: HashSet<(Path, usize)>,
    pub global_refs: HashSet<(Path, usize)>,
}

impl RefCollector {
    fn new() -> Self {
        Self {
            data_refs: HashSet::new(),
            global_refs: HashSet::new(),
        }
    }
}

/// Recursively collects `Variable::Data` and `Variable::Global` references.
trait CollectRefs {
    fn collect_refs(&self, collector: &mut RefCollector);
}

// --- Leaf ---

impl CollectRefs for Variable {
    fn collect_refs(&self, collector: &mut RefCollector) {
        match self {
            Variable::Data(path, idx) => {
                collector.data_refs.insert((path.clone(), *idx));
            }
            Variable::Global(path, idx) => {
                collector.global_refs.insert((path.clone(), *idx));
            }
            Variable::Local(_) | Variable::Unit => {}
        }
    }
}

// --- Atom ---

impl CollectRefs for Atom {
    fn collect_refs(&self, collector: &mut RefCollector) {
        if let Atom::Variable(v) = self {
            v.collect_refs(collector);
        }
    }
}

// --- Value ---

impl CollectRefs for Value {
    fn collect_refs(&self, collector: &mut RefCollector) {
        match self {
            Value::Atom(a) => a.collect_refs(collector),
            Value::Call(c) => c.collect_refs(collector),
            Value::CExternCall(c) => c.collect_refs(collector),
            Value::Select(s) => s.collect_refs(collector),
            Value::Load(l) => l.src.collect_refs(collector),
            Value::Extract(e) => e.src.collect_refs(collector),
            Value::Lea(l) => l.var.collect_refs(collector),
            Value::GetField(g) => g.src.collect_refs(collector),
            Value::Cast(c) => c.src.collect_refs(collector),
            Value::BasicOp(b) => {
                for operand in &b.operands {
                    operand.collect_refs(collector);
                }
            }
            Value::Closure(c) => c.collect_refs(collector),
            Value::Malloc(m) => m.count.collect_refs(collector),
            Value::IntConvert(ic) => ic.value.collect_refs(collector),
            // Phi contains (block_label, local_idx) pairs — no Variable refs
            Value::Phi(_) => {}
            Value::Upgrade(v) => v.collect_refs(collector),
            // No nested refs
            Value::Empty | Value::VarRef(_) | Value::Type(_) => {}
        }
    }
}

impl CollectRefs for Call {
    fn collect_refs(&self, collector: &mut RefCollector) {
        for arg in &self.args {
            arg.collect_refs(collector);
        }
    }
}

impl CollectRefs for CExternCall {
    fn collect_refs(&self, collector: &mut RefCollector) {
        for arg in &self.args {
            arg.collect_refs(collector);
        }
    }
}

impl CollectRefs for Select {
    fn collect_refs(&self, collector: &mut RefCollector) {
        self.cond.collect_refs(collector);
        self.then.collect_refs(collector);
        self.els.collect_refs(collector);
    }
}

impl CollectRefs for Closure {
    fn collect_refs(&self, collector: &mut RefCollector) {
        self.env.collect_refs(collector);
    }
}

// --- Inst ---

impl CollectRefs for Inst {
    fn collect_refs(&self, collector: &mut RefCollector) {
        match self {
            Inst::MemCopy(dst, src, size) => {
                dst.collect_refs(collector);
                src.collect_refs(collector);
                size.collect_refs(collector);
            }
            Inst::Store(s) => {
                s.dst.collect_refs(collector);
                s.value.collect_refs(collector);
            }
            Inst::Insert(i) => {
                i.src.collect_refs(collector);
                i.value.collect_refs(collector);
            }
            Inst::SetField(s) => {
                s.dst.collect_refs(collector);
                s.value.collect_refs(collector);
            }
            Inst::StructInit(v, _) => v.collect_refs(collector),
            Inst::SetLocal(_, v) | Inst::SetGlobal(_, v) => v.collect_refs(collector),
            Inst::Return(v) | Inst::IncRef(v, _) | Inst::DecRef(v, _) => v.collect_refs(collector),
            Inst::Call(c) => c.collect_refs(collector),
            Inst::CExternCall(c) => c.collect_refs(collector),
            Inst::Break(b) => {
                if let Some(operand) = &b.operand {
                    operand.collect_refs(collector);
                }
            }
            Inst::Free(_) | Inst::If(_) | Inst::Goto(_) => {}
        }
    }
}

// --- Containers ---

impl CollectRefs for Block {
    fn collect_refs(&self, collector: &mut RefCollector) {
        for inst in self.iter() {
            inst.collect_refs(collector);
        }
    }
}

impl CollectRefs for Func {
    fn collect_refs(&self, collector: &mut RefCollector) {
        for block in &self.blocks {
            block.collect_refs(collector);
        }
    }
}

impl CollectRefs for Global {
    fn collect_refs(&self, collector: &mut RefCollector) {
        self.init_value.collect_refs(collector);
    }
}

// --- Program::tree_shake ---

/// The root set of items to keep during tree-shaking.
///
/// For library builds, this is the snapshot of own func/extern names captured
/// before merging dependency programs. For executable builds, the root is
/// derived from `_start` automatically.
pub struct RootSet {
    pub func_names: HashSet<Path>,
    pub extern_names: HashSet<Path>,
}

impl Program {
    /// Snapshots the current func and extern names as a root set.
    ///
    /// Call this **before** `extend()`ing dependency programs so the snapshot
    /// captures only the library's own items.
    pub fn snapshot_root_set(&self) -> RootSet {
        RootSet {
            func_names: self.funcs.iter().map(|f| f.name.clone()).collect(),
            extern_names: self.extern_map.keys().cloned().collect(),
        }
    }

    /// Removes unreachable functions, data, globals, and externs from the program.
    ///
    /// If `root_set` is provided, it is used as the root set (library builds).
    /// Otherwise, the root is derived from `_start` (executable builds).
    pub fn tree_shake(&mut self, root_set: Option<&RootSet>) {
        let total_funcs = self.funcs.len();
        let total_data = self.data.len();
        let total_globals = self.globals.len();
        let total_externs = self.externs.len();

        // Phase 1: Collect reachable functions via DFS through symbols
        let fn_map: HashMap<Path, usize> = self
            .funcs
            .iter()
            .enumerate()
            .map(|(i, f)| (f.name.clone(), i))
            .collect();

        let mut reachable: HashSet<Path> = HashSet::new();
        let mut stack: Vec<Path> = Vec::new();

        if let Some(roots) = root_set {
            // Library: root is the snapshot of own items taken before extend()
            for name in &roots.func_names {
                stack.push(name.clone());
            }
            for name in &roots.extern_names {
                reachable.insert(name.clone());
            }
        } else if self.start_idx >= 0 {
            // Executable: root is _start
            stack.push(self.funcs[self.start_idx as usize].name.clone());
        }

        while let Some(path) = stack.pop() {
            if reachable.insert(path.clone()) {
                // Follow function symbols
                if let Some(&idx) = fn_map.get(&path) {
                    for sym in self.funcs[idx].symbols.iter() {
                        stack.push(sym.clone());
                    }
                }
                // Follow poly_fn_map specializations (pre-mono).
                // poly_fn_map keys are unmangled, but symbols are mangled,
                // so strip to names-only for the lookup.
                if let Some(indices) = self.poly_fn_map.get(&path.with_names_only()) {
                    for &idx in indices {
                        if idx < self.funcs.len() {
                            stack.push(self.funcs[idx].name.clone());
                        }
                    }
                }
            }
        }

        // Phase 2: Collect referenced data & globals from reachable functions
        let mut collector = RefCollector::new();
        for func in &self.funcs {
            if reachable.contains(&func.name) {
                func.collect_refs(&mut collector);
            }
        }
        // Also collect from reachable globals' init values
        for global in &self.globals {
            if collector.global_refs.contains(&global.key()) {
                global.collect_refs(&mut collector);
            }
        }

        // Phase 3: Filter in-place

        // Funcs: retain reachable, build index remap
        let mut index_remap: HashMap<usize, usize> = HashMap::new();
        let old_funcs = std::mem::take(&mut self.funcs);
        for (old_idx, func) in old_funcs.into_iter().enumerate() {
            if reachable.contains(&func.name) {
                let new_idx = self.funcs.len();
                index_remap.insert(old_idx, new_idx);
                self.funcs.push(func);
            }
        }

        // Remap special indices
        self.start_idx = if self.start_idx >= 0 {
            index_remap
                .get(&(self.start_idx as usize))
                .map(|&i| i as i64)
                .unwrap_or(-1)
        } else {
            -1
        };
        self.module_main_idx = if self.module_main_idx >= 0 {
            index_remap
                .get(&(self.module_main_idx as usize))
                .map(|&i| i as i64)
                .unwrap_or(-1)
        } else {
            -1
        };
        self.user_main_idx = if self.user_main_idx >= 0 {
            index_remap
                .get(&(self.user_main_idx as usize))
                .map(|&i| i as i64)
                .unwrap_or(-1)
        } else {
            -1
        };

        // Rebuild poly_fn_map with remapped indices
        let old_poly = std::mem::take(&mut self.poly_fn_map);
        for (name, indices) in old_poly {
            let remapped: Vec<usize> = indices
                .into_iter()
                .filter_map(|i| index_remap.get(&i).copied())
                .collect();
            if !remapped.is_empty() {
                self.poly_fn_map.insert(name, remapped);
            }
        }

        // Data: retain referenced
        self.data.retain(|d| collector.data_refs.contains(&d.key()));

        // Globals: retain referenced
        self.globals
            .retain(|g| collector.global_refs.contains(&g.key()));

        // Externs: retain those reachable by either their extern_map key (qualified
        // name, e.g. `testing::assert`) or their link name (e.g. `assert`).
        // Call sites add the link name to symbols, while library root sets use
        // the qualified extern_map key.
        let old_extern_map = std::mem::take(&mut self.extern_map);
        let old_externs = std::mem::take(&mut self.externs);
        for (map_key, old_idx) in old_extern_map {
            let ext = &old_externs[old_idx];
            if reachable.contains(&map_key) || reachable.contains(&ext.name) {
                let new_idx = self.externs.len();
                self.extern_map.insert(map_key, new_idx);
                self.externs.push(ext.clone());
            }
        }

        log::debug!(
            "tree_shake: {} -> {} funcs, {} -> {} data, {} -> {} globals, {} -> {} externs",
            total_funcs,
            self.funcs.len(),
            total_data,
            self.data.len(),
            total_globals,
            self.globals.len(),
            total_externs,
            self.externs.len(),
        );
    }
}
