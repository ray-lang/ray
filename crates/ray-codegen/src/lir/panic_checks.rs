use std::collections::HashSet;

use ray_lir::{
    Atom, Block, Call, Func, If, Inst, IntrinsicKind, Local, Program, Size, TraceEntry, Value,
};
use ray_shared::{pathlib::Path, ty::Ty};
use ray_typing::types::TyScheme;

/// Insert flag checks after every call to a panicable function.
///
/// For each panicable call site in block B at position `i`:
///   - Split B: keep instructions [0..=i], drain [i+1..] into a new `continue_block`
///   - Append `$flag = call __panic_is_unwinding()` to B
///   - Terminate B with `If($flag, fail_block, continue_block)`
///   - `fail_block` returns `Value::Uninit` to propagate the unwind
///   - `continue_block` gets the drained tail and is processed in the next iteration
///
/// Functions that explicitly call `__panic_is_unwinding` (e.g. `recover`) are
/// exempt — they manage their own flag check.
pub fn insert_panic_checks(program: &mut Program) {
    let panicable = compute_panicable_set(program);
    for func_idx in 0..program.funcs.len() {
        if is_panic_self_managed(&program.funcs[func_idx]) {
            continue;
        }
        let ret_ty = program.funcs[func_idx]
            .ty
            .mono()
            .get_fn_ret_ty()
            .cloned()
            .unwrap_or_else(Ty::never);
        insert_checks_for_func(&mut program.funcs[func_idx], &panicable, &ret_ty);
    }
    for func in &mut program.funcs {
        insert_panic_site_traces(func);
    }
}

fn insert_checks_for_func(func: &mut Func, panicable: &HashSet<String>, ret_ty: &Ty) {
    let mut block_idx = 0;
    while block_idx < func.blocks.len() {
        if let Some(split_pos) = find_panicable_call(&func.blocks[block_idx], panicable) {
            split_block_at(func, block_idx, split_pos, ret_ty);
        }
        block_idx += 1;
    }
}

/// Splits block `block_idx` at instruction index `call_pos`, inserting a
/// flag check and branching to a fail block or a continue block.
fn split_block_at(func: &mut Func, block_idx: usize, call_pos: usize, ret_ty: &Ty) {
    let trace_entry = trace_entry_for_call(&func.blocks[block_idx][call_pos], func);
    let tail: Vec<Inst> = func.blocks[block_idx].drain(call_pos + 1..).collect();

    let flag_idx = func.locals.len();
    func.locals
        .push(Local::new(flag_idx, TyScheme::from(Ty::bool())));

    let fail_label = func.blocks.len();
    let continue_label = fail_label + 1;

    let is_unwinding_path = Path::from("__panic_is_unwinding");
    func.symbols.insert(is_unwinding_path.clone());
    let check_call = Call::new(
        is_unwinding_path,
        vec![],
        TyScheme::from(Ty::Func(vec![], Box::new(Ty::bool()))),
        None,
    );
    func.blocks[block_idx].push(Inst::SetLocal(flag_idx, Value::Call(check_call)));
    func.blocks[block_idx].push(Inst::If(If::new(flag_idx, fail_label, continue_label)));

    let mut fail_block = Block::new(fail_label);
    fail_block.push(Inst::PushTraceEntry(trace_entry));
    fail_block.push(Inst::Return(uninit_return(ret_ty)));
    func.blocks.push(fail_block);

    let mut continue_block = Block::new(continue_label);
    for inst in tail {
        continue_block.push(inst);
    }
    func.blocks.push(continue_block);
}

/// Returns the appropriate `Value` for a dummy return on the unwind path.
fn uninit_return(ty: &Ty) -> Value {
    if ty.is_unit() || ty.is_never() {
        return Value::Empty;
    }
    match ty {
        Ty::Ref(_)
        | Ty::MutRef(_)
        | Ty::IdRef(_)
        | Ty::RawPtr(_)
        | Ty::Borrow(_)
        | Ty::BorrowMut(_)
        | Ty::Func(_, _) => Atom::NilConst.into(),
        Ty::Const(path) => match path.to_string().as_str() {
            "bool" => Atom::BoolConst(false).into(),
            "i8" | "u8" => Atom::IntConst(0, Size::bytes(1)).into(),
            "i16" | "u16" => Atom::IntConst(0, Size::bytes(2)).into(),
            "i32" | "u32" | "char" => Atom::IntConst(0, Size::bytes(4)).into(),
            "i64" | "u64" | "int" | "uint" => Atom::IntConst(0, Size::bytes(8)).into(),
            _ => Value::Uninit(ty.clone()),
        },
        _ => Value::Uninit(ty.clone()),
    }
}

fn is_panic_self_managed(func: &Func) -> bool {
    func.blocks.iter().flat_map(|b| b.iter()).any(|inst| {
        inst.get_call()
            .map(|c| {
                matches!(
                    IntrinsicKind::from_path(&c.fn_name),
                    Some(IntrinsicKind::PanicIsUnwinding)
                )
            })
            .unwrap_or(false)
    })
}

fn compute_panicable_set(program: &Program) -> HashSet<String> {
    let mut panicable: HashSet<String> = program
        .funcs
        .iter()
        .filter(|f| {
            f.blocks.iter().flat_map(|b| b.iter()).any(|inst| {
                inst.get_call()
                    .map(|c| {
                        matches!(
                            IntrinsicKind::from_path(&c.fn_name),
                            Some(IntrinsicKind::Panic)
                        )
                    })
                    .unwrap_or(false)
            })
        })
        .map(|f| f.name.to_string())
        .collect();

    loop {
        let mut added = false;
        for func in &program.funcs {
            let name = func.name.to_string();
            if panicable.contains(&name) {
                continue;
            }
            let is_panicable =
                func.blocks
                    .iter()
                    .flat_map(|b| b.iter())
                    .any(|inst| match inst.get_call() {
                        Some(call) if call.fn_ref.is_some() => true,
                        Some(call) => panicable.contains(&call.fn_name.to_string()),
                        None => false,
                    });
            if is_panicable {
                panicable.insert(name);
                added = true;
            }
        }
        if !added {
            break;
        }
    }

    panicable
}

fn find_panicable_call(block: &Block, panicable: &HashSet<String>) -> Option<usize> {
    block
        .iter()
        .enumerate()
        .find_map(|(i, inst)| is_panicable_call(inst, panicable).then_some(i))
}

fn is_panicable_call(inst: &Inst, panicable: &HashSet<String>) -> bool {
    let call = match inst.get_call() {
        Some(c) => c,
        None => return false,
    };
    if matches!(
        IntrinsicKind::from_path(&call.fn_name),
        Some(
            IntrinsicKind::PanicIsUnwinding
                | IntrinsicKind::PanicClearUnwinding
                | IntrinsicKind::PanicLoadMessage
                | IntrinsicKind::PanicPrintTrace
        )
    ) {
        return false;
    }
    if call.fn_ref.is_some() {
        return true;
    }
    panicable.contains(&call.fn_name.to_string())
}

/// Insert a trace entry after every direct `panic()` call so the originating
/// function appears as the first frame in the stack trace.
fn insert_panic_site_traces(func: &mut Func) {
    let fn_display_name = func.display_path.to_string();
    let mut insertions: Vec<(usize, usize, TraceEntry)> = Vec::new();
    for (block_idx, block) in func.blocks.iter().enumerate() {
        for (inst_idx, inst) in block.iter().enumerate() {
            let call = match inst.get_call() {
                Some(c) => c,
                None => continue,
            };
            if !matches!(
                IntrinsicKind::from_path(&call.fn_name),
                Some(IntrinsicKind::Panic)
            ) {
                continue;
            }
            let entry = TraceEntry::from_call(call, fn_display_name.clone());
            insertions.push((block_idx, inst_idx + 1, entry));
        }
    }
    // Insert in reverse order so indices stay valid.
    for (block_idx, inst_idx, entry) in insertions.into_iter().rev() {
        func.blocks[block_idx].insert(inst_idx, Inst::PushTraceEntry(entry));
    }
}

fn trace_entry_for_call(inst: &Inst, func: &Func) -> TraceEntry {
    let call = inst.get_call().expect("expected a call instruction");
    TraceEntry::from_call(call, func.display_path.to_string())
}
