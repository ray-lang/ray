use std::{
    collections::{HashMap, HashSet},
    ops::DerefMut,
};

use lir::IterCalls;

use crate::{
    ast::{Node, Path},
    lir::{self, NamedInst},
    sema,
    typing::{ty::Ty, ApplySubst},
};

#[derive(Debug)]
struct PolyFnRef<'a> {
    value: &'a mut lir::Call,
    path: Path,
    poly_ty: Ty,   // the polymorphic type
    callee_ty: Ty, // the type of the callee (which may be polymorphic as well)
}

#[derive(Debug)]
pub struct Monomorphizer {
    extern_set: HashSet<Path>,
    name_set: HashSet<Path>,
    poly_fn_map: HashMap<Path, Node<lir::Func>>, // polymorphic functions
    poly_mono_fn_idx: HashMap<Path, Vec<Path>>, // a mapping of polymorphic functions to monomorphizations
    mono_poly_fn_idx: HashMap<Path, Path>, // a mapping of monomorphic functions to their polymorphic counterpart
    mono_fn_ty_map: HashMap<Path, Ty>,     // map of all monomorphic function types
}

impl Monomorphizer {
    pub fn new(prog: &lir::Program) -> Monomorphizer {
        let poly_fn_map = prog
            .poly_fn_map
            .iter()
            .map(|(n, i)| (n.clone(), prog.funcs[*i].clone()))
            .collect();

        let name_set = prog.funcs.iter().map(|f| f.name.clone()).collect();
        log::debug!("name set: {:#?}", name_set);
        let mut extern_set = prog.extern_set.clone();
        extern_set.extend(prog.trait_member_set.clone());
        Monomorphizer {
            poly_fn_map,
            name_set,
            extern_set,
            poly_mono_fn_idx: HashMap::new(),
            mono_poly_fn_idx: HashMap::new(),
            mono_fn_ty_map: HashMap::new(),
        }
    }

    fn add_mono_fn_mapping(&mut self, poly_name: &Path, mono_name: &Path) {
        if !self.poly_mono_fn_idx.contains_key(poly_name) {
            self.poly_mono_fn_idx
                .insert(poly_name.clone(), vec![mono_name.clone()]);
        } else {
            self.poly_mono_fn_idx
                .get_mut(poly_name)
                .unwrap()
                .push(mono_name.clone());
        }
    }

    pub fn monomorphize(&mut self, entry: &mut Node<lir::Func>) -> Vec<Node<lir::Func>> {
        let mut funcs = vec![];
        self.monomorphize_func(entry, &mut funcs);
        funcs
    }

    fn monomorphize_func(&mut self, func: &mut Node<lir::Func>, funcs: &mut Vec<Node<lir::Func>>) {
        let mut symbols = func.symbols.clone();
        let mut poly_refs = vec![];
        let func_name = func.name.clone();
        self.collect(func.iter_calls(), &mut poly_refs);

        for mut poly_ref in poly_refs {
            log::debug!("[monomorphize] {:?}", poly_ref);
            let (poly_name, mono_name) = self.monomorphize_ref(&mut poly_ref, funcs);
            log::debug!("symbols for `{}`: {:?}", func_name, symbols);
            log::debug!("poly_name: {}", poly_name);
            log::debug!("mono_name: {}", mono_name);

            let base_poly_name = poly_name.without_tyargs();

            // remove from the name set
            self.name_set.remove(&base_poly_name);
            self.name_set.insert(mono_name.clone());

            // remove from the function symbols
            symbols.remove(&poly_name);
            symbols.remove(&base_poly_name);
            symbols.insert(mono_name);
        }

        func.symbols = symbols;
    }

    fn monomorphize_ref(
        &mut self,
        poly_ref: &mut PolyFnRef<'_>,
        funcs: &mut Vec<Node<lir::Func>>,
    ) -> (Path, Path) {
        // NOTE: unless there's a bug in the compiler, the callee function type is always monomorphic
        // Function types that make it here are either contained in a pure-monomorphic
        // function, which means that the call will have a concrete type, or
        // the type is contained in a monomorphized polymorphic function in which case
        // the function type has been monomorphized previously

        // check that the callee function type is monomorphic
        if poly_ref.callee_ty.is_polymorphic() {
            panic!(
                "cannot monomorphize function where the callee type is polymorphic: {}",
                poly_ref.callee_ty
            );
        }

        // get the polymorphic name
        let poly_fqn = poly_ref.value.get_name().without_tyargs();
        let poly_base_name = poly_fqn.clone();
        let poly_name = sema::fn_name(&poly_base_name, &poly_ref.poly_ty);

        // get the monomorphized name using a substitution
        let subst = poly_ref
            .poly_ty
            .mgu(&poly_ref.callee_ty)
            .ok()
            .unwrap_or_default();
        log::debug!("[monomorphize] subst = {:#?}", subst);
        let mono_fqn = poly_fqn.clone().apply_subst(&subst);
        let mono_base_name = mono_fqn.clone();
        let mono_name = sema::fn_name(&mono_base_name, &poly_ref.callee_ty);

        // if self.name_set.contains(&mono_base_name) {
        //     mono_base_name.clone()
        // } else {
        //     sema::fn_name(&mono_base_name, &poly_ref.callee_ty)
        // };

        log::debug!("[monomorphize] poly_name = {}", poly_name);
        log::debug!("[monomorphize] mono_name = {}", mono_name);

        // set the name
        poly_ref.value.set_name(mono_name.clone());

        // make sure that the functions are not externs
        if self.extern_set.contains(&poly_base_name) || self.extern_set.contains(&poly_name) {
            return (poly_name, mono_name);
        }

        if self.extern_set.contains(&mono_base_name) {
            return (poly_name, mono_base_name);
        }

        if self.extern_set.contains(&mono_name) || self.name_set.contains(&mono_name) {
            return (poly_name, mono_name);
        }

        // add it to the map
        self.mono_poly_fn_idx
            .insert(poly_name.clone(), mono_name.clone());

        // make sure that there isn't already a monomorphized version
        if self.mono_fn_ty_map.contains_key(&mono_name) {
            return (poly_base_name, mono_name);
        }

        // get the polymorphic function from the index and add a mapping from poly to mono
        let mut mono_fn = self
            .poly_fn_map
            .get(&poly_fqn)
            .cloned()
            .expect(&format!("polymorphic function `{}` is undefined", poly_fqn));
        mono_fn.name = mono_name.clone();
        mono_fn.ty = poly_ref.callee_ty.clone();

        self.add_mono_fn_mapping(&poly_name, &mono_name);

        // apply the substitution to the function
        mono_fn = mono_fn.apply_subst(&subst);
        log::debug!(
            "symbols for `{}` after subst: {:?}",
            mono_name,
            mono_fn.symbols
        );

        // collect further polymorphic functions from the new monomorphized function
        self.monomorphize_func(&mut mono_fn, funcs);
        funcs.push(mono_fn);
        (poly_name, mono_name)
    }

    fn collect<'a, T>(&self, insts: T, poly_refs: &mut Vec<PolyFnRef<'a>>)
    where
        T: IntoIterator<Item = &'a mut lir::Inst>,
    {
        for inst in insts.into_iter() {
            log::debug!("[monomorphize] collect: {}", inst);
            match inst {
                lir::Inst::SetGlobal(_, v)
                | lir::Inst::SetLocal(_, v)
                | lir::Inst::IncRef(v, _)
                | lir::Inst::DecRef(v)
                | lir::Inst::Return(v) => self.add_ref_from_value(v, poly_refs),
                lir::Inst::Store(s) => self.add_ref_from_value(&mut s.value, poly_refs),
                lir::Inst::Call(call) => self.add_ref(poly_refs, call),

                lir::Inst::Free(_)
                | lir::Inst::CExternCall(_)
                | lir::Inst::MemCopy(_, _, _)
                | lir::Inst::If(_)
                | lir::Inst::Break(_)
                | lir::Inst::Goto(_)
                | lir::Inst::Halt => continue,
            }
        }
    }

    fn add_ref_from_value<'a>(
        &self,
        value: &'a mut lir::Value,
        poly_refs: &mut Vec<PolyFnRef<'a>>,
    ) {
        match value {
            lir::Value::Atom(a) => match a {
                lir::Atom::FuncRef(_) => todo!(),
                _ => {}
            },
            lir::Value::Call(call) => self.add_ref(poly_refs, call),
            lir::Value::CExternCall(_) => todo!(),
            _ => {}
        };
    }

    fn add_ref<'a>(&self, poly_refs: &mut Vec<PolyFnRef<'a>>, call: &'a mut lir::Call) {
        if call.fn_ref.is_some() {
            return;
        }
        let callee_ty = call.ty.clone();
        let poly_ty = unless!(&call.poly_ty).clone();
        let path = call.fn_name.clone();
        poly_refs.push(PolyFnRef {
            value: call,
            path,
            poly_ty,
            callee_ty,
        });
    }
}
