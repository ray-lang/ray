use std::{
    borrow::{BorrowMut, Cow},
    cell::{RefCell, RefMut},
    collections::{HashMap, HashSet},
    ops::DerefMut,
    rc::Rc,
};

use lir::IterCalls;
use top::{mgu, util::Join, Subst, Substitutable};

use crate::{
    ast::{Node, Path},
    convert::ToSet,
    lir::{self, GetLocals, NamedInst},
    sema,
    typing::ty::{Ty, TyScheme, TyVar},
};

#[derive(Debug)]
enum PolyValue<'a> {
    Call(&'a mut lir::Call),
    Global(usize),
}

#[derive(Debug)]
struct PolyRef<'a> {
    value: PolyValue<'a>,
    poly_ty: TyScheme,   // the polymorphic type
    callee_ty: TyScheme, // the type of the callee (which may be polymorphic as well)
}

#[derive(Debug)]
pub struct Monomorphizer<'p> {
    program: Rc<RefCell<&'p mut lir::Program>>,
    extern_set: HashSet<Path>,
    name_set: HashSet<Path>,
    poly_fn_map: HashMap<Path, Node<lir::Func>>, // polymorphic functions
    poly_global_map: HashMap<usize, lir::Global>, // polymorphic globals
    poly_mono_fn_idx: HashMap<Path, Vec<(Path, Ty)>>, // a mapping of polymorphic functions to monomorphizations
    mono_poly_fn_idx: HashMap<Path, Path>, // a mapping of monomorphic functions to their polymorphic counterpart
    mono_fn_ty_map: HashMap<Path, Ty>,     // map of all monomorphic function types
}

impl<'p> Monomorphizer<'p> {
    pub fn new(program: &'p mut lir::Program) -> Monomorphizer<'p> {
        // TODO: don't clone these into the Monomorphizer (reference them outside)
        let poly_fn_map = program
            .poly_fn_map
            .iter()
            .map(|(n, &i)| (n.clone(), program.funcs[i].clone()))
            .collect();

        let poly_global_map = program.globals.iter().map(|g| (g.idx, g.clone())).collect();

        let name_set = program.funcs.iter().map(|f| f.name.clone()).collect();
        log::debug!("name set: {:#?}", name_set);
        let mut extern_set = program.extern_map.keys().cloned().to_set();
        extern_set.extend(program.trait_member_set.clone());
        Monomorphizer {
            program: Rc::new(RefCell::new(program)),
            poly_fn_map,
            poly_global_map,
            name_set,
            extern_set,
            poly_mono_fn_idx: HashMap::new(),
            mono_poly_fn_idx: HashMap::new(),
            mono_fn_ty_map: HashMap::new(),
        }
    }

    fn add_mono_fn_mapping(&mut self, poly_name: &Path, mono_name: &Path, mono_ty: Ty) {
        self.poly_mono_fn_idx
            .entry(poly_name.clone())
            .or_default()
            .push((mono_name.clone(), mono_ty));
    }

    pub fn mono_fn_externs(self) -> HashMap<Path, Vec<(Path, Ty)>> {
        let extern_set = self.extern_set;
        self.poly_mono_fn_idx
            .into_iter()
            .flat_map(|(poly_fn, mono_fns)| {
                if extern_set.contains(&poly_fn) {
                    Some((poly_fn, mono_fns))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn monomorphize(&mut self) -> Vec<Node<lir::Func>> {
        /*
         * Due to changes in the solver, non-function types can also be quantified and/or qualified types.
         * This means that during code generation, values can be polymorphic and must be monomorphized in
         * the same way that polymorphic functions are monomorphized. This _should_ be relatively
         * straightforward: modify the monomorphization process to search for values (not just functions)
         * that are polymorphic. These can be then treated as polymorphic "call sites" and thus be
         * branched accordingly.
         */

        let mut globals = vec![];
        let mut funcs = vec![];
        let rc_prog = Rc::clone(&self.program);
        let mut prog = RefCell::borrow_mut(&rc_prog);

        // for global in prog.globals.iter_mut() {
        //     if global.ty.is_polymorphic() {
        //         self.monomorphize_value(&mut global.init_value, &mut global.ty);
        //     }
        // }

        // monomorphize polymorphic functions that are called from non-polymorphic functions
        for func in prog.funcs.iter_mut() {
            // NOTE: only calls within _monomorphic_ functions can be monomorphized
            if !func.ty.is_polymorphic() {
                self.monomorphize_func(func, &mut funcs, &mut globals);
            }
        }

        funcs
    }

    fn monomorphize_func(
        &mut self,
        func: &mut Node<lir::Func>,
        funcs: &mut Vec<Node<lir::Func>>,
        globals: &mut Vec<lir::Global>,
    ) {
        let mut symbols = func.symbols.clone();
        let mut poly_refs = vec![];
        let mut locals = HashMap::new();
        let func_name = func.name.clone();
        self.collect(func.into_iter(), &mut poly_refs);

        for mut poly_ref in poly_refs {
            log::debug!("[monomorphize] {:?}", poly_ref);
            if let Some((poly_name, mono_name)) =
                self.monomorphize_ref(&mut poly_ref, &mut locals, funcs, globals)
            {
                log::debug!("symbols for `{}`: {:?}", func_name, symbols);
                log::debug!("poly_name: {}", poly_name);
                log::debug!("mono_name: {}", mono_name);
                if poly_name == mono_name {
                    continue;
                }

                let base_poly_name = poly_name.without_func_type();

                // remove from the name set
                self.name_set.remove(&base_poly_name);
                self.name_set.insert(mono_name.clone());

                // remove from the function symbols
                symbols.remove(&poly_name);
                symbols.remove(&base_poly_name);
                symbols.insert(mono_name);
            }
        }

        // now for each local in the map, set the type of the local in the function
        for (loc, ty) in locals {
            func.set_ty_of_local(loc, ty);
        }

        func.symbols = symbols;
    }

    fn monomorphize_ref(
        &mut self,
        poly_ref: &mut PolyRef<'_>,
        locals: &mut HashMap<usize, TyScheme>,
        funcs: &mut Vec<Node<lir::Func>>,
        globals: &mut Vec<lir::Global>,
    ) -> Option<(Path, Path)> {
        match &mut poly_ref.value {
            PolyValue::Call(call) => Some(self.monomorphize_call(
                call,
                &poly_ref.poly_ty,
                &mut poly_ref.callee_ty,
                locals,
                funcs,
                globals,
            )),
            PolyValue::Global(_) => {
                todo!()
                // self.monomorphize_global_ref(*global, &mut poly_ref.callee_ty, globals);
                // None
            }
        }
    }

    fn monomorphize_call(
        &mut self,
        call: &mut lir::Call,
        poly_ty: &TyScheme,
        callee_ty: &mut TyScheme,
        locals: &mut HashMap<usize, TyScheme>,
        funcs: &mut Vec<Node<lir::Func>>,
        globals: &mut Vec<lir::Global>,
    ) -> (Path, Path) {
        // NOTE: unless there's a bug in the compiler, the callee function type is always monomorphic
        // Function types that make it here are either contained in a pure-monomorphic
        // function, which means that the call will have a concrete type, or
        // the type is contained in a monomorphized polymorphic function in which case
        // the function type has been monomorphized previously

        let poly_fqn = call.orig_name().without_func_type();
        log::debug!("[monomorphize] poly_fqn: {}", poly_fqn);
        log::debug!("[monomorphize] poly_ty: {}", poly_ty);
        log::debug!("[monomorphize] callee_ty: {}", callee_ty);

        // check that the callee function type is monomorphic
        if callee_ty.is_polymorphic() {
            log::debug!("callee type is not monomorphic: {}", callee_ty);
            log::debug!("   here's the polymorphic type: {}", poly_ty);
            panic!(
                "cannot monomorphize function where the callee type is polymorphic: {}",
                callee_ty
            );
        }

        // get the polymorphic name
        let poly_base_name = poly_fqn.clone();
        let poly_name = sema::fn_name(&poly_base_name, poly_ty);

        // get the monomorphized name using a substitution
        let (_, subst) = mgu(poly_ty.mono(), callee_ty.mono())
            .ok()
            .unwrap_or_default();
        log::debug!("[monomorphize] subst = {:#?}", subst);
        let mut mono_fqn = poly_fqn.clone();
        mono_fqn.apply_subst(&subst);
        let mono_base_name = mono_fqn.clone();
        let mono_name = sema::fn_name(&mono_base_name, callee_ty);
        let mono_ty = callee_ty.clone();

        log::debug!("[monomorphize] poly_name = {}", poly_name);
        log::debug!("[monomorphize] mono_name = {}", mono_name);

        // make sure that the functions are not externs
        let (poly_name, mono_name) = if self.extern_set.contains(&poly_name)
            || self.extern_set.contains(&mono_name)
            || self.name_set.contains(&mono_name)
        {
            (poly_name, mono_name)
        } else if self.extern_set.contains(&mono_base_name) {
            (poly_name, mono_base_name)
        } else if self.extern_set.contains(&poly_base_name) {
            (poly_base_name, mono_name)
        } else if self.mono_fn_ty_map.contains_key(&mono_name) {
            // make sure that there isn't already a monomorphized version
            (poly_base_name, mono_name)
        } else {
            // get the polymorphic function from the index and add a mapping from poly to mono
            let mut mono_fn = self.poly_fn_map.get(&poly_fqn).cloned().expect(&format!(
                "polymorphic function `{}` is undefined. here are the defined functions:\n{}",
                poly_fqn,
                self.poly_fn_map
                    .keys()
                    .map(|a| format!("  {}", a))
                    .join("\n")
            ));
            mono_fn.name = mono_name.clone();
            mono_fn.ty = mono_ty.clone();

            // apply the substitution to the function
            mono_fn.apply_subst(&subst);
            log::debug!(
                "symbols for `{}` after subst: {:?}",
                mono_name,
                mono_fn.symbols
            );

            // collect further polymorphic functions from the new monomorphized function
            self.monomorphize_func(&mut mono_fn, funcs, globals);
            funcs.push(mono_fn);
            (poly_name, mono_name)
        };

        // set the name
        call.set_name(mono_name.clone());

        for (idx, arg) in call.args.iter().enumerate() {
            if let &lir::Variable::Local(loc) = arg {
                if let Some(ty) = mono_ty.mono().get_func_param(idx).cloned() {
                    log::debug!("adding local with type {}: {}", loc, ty);
                    // FIXME: what if the loc is already in the map with another type?
                    locals.insert(loc, ty.into());
                }
            }
        }

        // add it to the map
        self.mono_poly_fn_idx
            .insert(poly_name.clone(), mono_name.clone());
        self.add_mono_fn_mapping(&poly_name, &mono_name, mono_ty.into_mono());
        (poly_name, mono_name)
    }

    fn monomorphize_global_ref(
        &mut self,
        global: usize,
        ty: &mut Ty,
        globals: &mut Vec<lir::Global>,
    ) {
        todo!()
        // let subst = apply_trait_defaults(ty);
        // if ty.is_polymorphic() {
        //     panic!(
        //         "cannot monomorphize value where the type is polymorphic: {}",
        //         ty
        //     );
        // }

        // let mut global = self
        //     .poly_global_map
        //     .get(&global)
        //     .cloned()
        //     .expect("global is not defined");
        // if let Some(subst) = subst {
        //     global.apply_subst_mut(&subst);
        // }

        // globals.push(global);
    }

    fn monomorphize_value(&mut self, value: &mut lir::Value, poly_ty: &mut Ty) {
        todo!()
        // let subst = apply_trait_defaults(poly_ty);
        // if poly_ty.is_polymorphic() {
        //     panic!(
        //         "cannot monomorphize value where the type is polymorphic: {}",
        //         poly_ty
        //     );
        // }

        // if let Some(subst) = subst {
        //     value.apply_subst_mut(&subst);
        // }
    }

    fn collect<'a, T>(&self, insts: T, poly_refs: &mut Vec<PolyRef<'a>>)
    where
        T: Iterator<Item = &'a mut lir::Inst>,
    {
        for inst in insts {
            log::debug!("[monomorphize] collect: {}", inst);
            match inst {
                lir::Inst::SetGlobal(_, v)
                | lir::Inst::SetLocal(_, v)
                | lir::Inst::IncRef(v, _)
                | lir::Inst::DecRef(v)
                | lir::Inst::Return(v) => self.add_ref_from_value(v, poly_refs),
                lir::Inst::Store(s) => self.add_ref_from_value(&mut s.value, poly_refs),
                lir::Inst::SetField(s) => self.add_ref_from_value(&mut s.value, poly_refs),
                lir::Inst::Call(call) => self.add_call_ref(poly_refs, call),

                lir::Inst::Free(_)
                | lir::Inst::CExternCall(_)
                | lir::Inst::MemCopy(_, _, _)
                | lir::Inst::If(_)
                | lir::Inst::Break(_)
                | lir::Inst::Goto(_) => continue,
            }
        }
    }

    fn add_ref_from_value<'a>(&self, value: &'a mut lir::Value, poly_refs: &mut Vec<PolyRef<'a>>) {
        match value {
            lir::Value::Atom(a) => match a {
                lir::Atom::FuncRef(_) => todo!(),
                _ => {}
            },
            lir::Value::Call(call) => self.add_call_ref(poly_refs, call),
            lir::Value::CExternCall(_) => todo!(),
            _ => {}
        };
    }

    fn add_call_ref<'a>(&self, poly_refs: &mut Vec<PolyRef<'a>>, call: &'a mut lir::Call) {
        if call.fn_ref.is_some() {
            return;
        }
        let callee_ty = call.ty.clone();
        let poly_ty = unless!(&call.poly_ty).clone();
        poly_refs.push(PolyRef {
            value: PolyValue::Call(call),
            poly_ty,
            callee_ty,
        });
    }
}

// fn apply_trait_defaults(ty: &mut TyScheme) -> Option<Subst<TyVar, Ty>> {
//     if ty.qualifiers().is_empty() {
//         return None;
//     }

//     let subst = ty
//         .qualifiers()
//         .iter()
//         .flat_map(|p| {
//             p.type_params().and_then(|ty_params| {
//                 if p.is_int_trait() {
//                     Some((variant!(&ty_params[0], if Ty::Var(a)).clone(), Ty::int()))
//                 } else if p.is_float_trait() {
//                     Some((variant!(&ty_params[0], if Ty::Var(a)).clone(), Ty::float()))
//                 } else {
//                     None
//                 }
//             })
//         })
//         .collect::<Subst<TyVar, Ty>>();
//     ty.apply_subst(&subst);
//     Some(subst)
// }
