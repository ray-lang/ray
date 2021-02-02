use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    ast::{Node, SourceInfo},
    lir::{self, Inst, Store, Value},
};

use super::Optimize;

pub(super) struct Inline();

impl Optimize for Inline {
    fn level(&self) -> usize {
        0
    }

    fn optimize_func(&self, _: &mut lir::Func) {
        unreachable!("this should not be called")
    }

    fn optimize(&self, prog: &mut lir::Program) {
        // walk the program and find calls to inline
        let func_names = prog
            .funcs
            .iter()
            .map(|f| f.name.clone())
            .collect::<Vec<_>>();
        let mut funcs = prog
            .funcs
            .drain(..)
            .map(|f| (f.name.clone(), Rc::new(RefCell::new(f))))
            .collect::<HashMap<_, _>>();

        for f in funcs.values().cloned() {
            let mut locals = f.borrow().locals.clone();
            let mut fn_mut = f.borrow_mut();
            let body = &mut fn_mut.body.instructions;

            let mut idx = 0;
            let mut removed_symbols = HashSet::new();
            while idx < body.len() {
                let inst = &mut body[idx];
                let info = inst.info.clone();
                if let Some((loc, fn_name, args)) = match &mut inst.value {
                    Inst::SetGlobal(loc, Value::Call(c)) => Some((
                        Some(lir::Variable::Global(*loc)),
                        c.fn_name.clone(),
                        c.args.clone(),
                    )),
                    Inst::SetLocal(loc, Value::Call(c)) => Some((
                        Some(lir::Variable::Local(*loc)),
                        c.fn_name.clone(),
                        c.args.clone(),
                    )),
                    Inst::Value(Value::Call(c))
                    | Inst::IncRef(Value::Call(c), _)
                    | Inst::DecRef(Value::Call(c))
                    | Inst::Return(Value::Call(c))
                    | Inst::Store(Store {
                        value: Value::Call(c),
                        ..
                    }) => Some((None, c.fn_name.clone(), c.args.clone())),
                    _ => None,
                } {
                    let args = args;
                    if let Some(new_inst) = self.inline_call(
                        &mut inst.value,
                        &info,
                        fn_name.clone(),
                        args,
                        loc,
                        &mut locals,
                        &funcs,
                    ) {
                        removed_symbols.insert(fn_name);
                        body.splice(idx..idx, new_inst);
                    }
                }
                idx += 1;
            }

            for f in removed_symbols {
                fn_mut.symbols.remove(&f);
            }
            fn_mut.locals = locals;
        }

        // insert in the same order
        for name in func_names {
            if let Some(f) = funcs.remove(&name) {
                prog.funcs.push(Rc::try_unwrap(f).unwrap().into_inner());
            }
        }
    }
}

impl Inline {
    fn inline_call(
        &self,
        inst: &mut Inst,
        info: &SourceInfo,
        fn_name: String,
        args: Vec<lir::Variable>,
        loc: Option<lir::Variable>,
        locals: &mut Vec<lir::Local>,
        funcs: &HashMap<String, Rc<RefCell<lir::Func>>>,
    ) -> Option<Vec<Node<Inst, SourceInfo>>> {
        if let Some(f) = funcs.get(&fn_name) {
            if f.borrow().has_inline() {
                let f = f.borrow().clone();
                let (new_locs, new_inst, ret_val) = f.inline(args, info.clone(), locals.len());
                locals.extend(new_locs);

                let src = match loc {
                    Some(lir::Variable::Local(loc)) => Inst::SetLocal(loc, ret_val),
                    Some(lir::Variable::Global(loc)) => Inst::SetGlobal(loc, ret_val),
                    _ => Inst::Value(ret_val),
                };
                let _ = std::mem::replace(inst, src);
                Some(new_inst)
            } else {
                None
            }
        } else {
            None
        }
    }
}
