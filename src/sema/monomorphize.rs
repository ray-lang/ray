use std::{
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
    rc::Rc,
};

use crate::{
    ast::{Node, Path, SourceInfo},
    lir::{self, NamedInst},
    sema,
    strutils::rand_string,
    typing::{state::TyVarFactory, traits::Polymorphize, ty::Ty, ApplySubst},
};

#[derive(Debug)]
struct PolyFnRef<'a> {
    value: &'a mut lir::Value,
    path: Path,
    poly_ty: Ty,   // the polymorphic type
    callee_ty: Ty, // the type of the callee (which may be polymorphic as well)
}

#[derive(Debug)]
pub struct Monomorphizer {
    extern_set: HashSet<String>,
    name_set: HashSet<String>,
    poly_fn_map: HashMap<String, lir::Func>, // polymorphic functions
    poly_mono_fn_idx: HashMap<String, Vec<String>>, // a mapping of polymorphic functions to monomorphizations
    mono_poly_fn_idx: HashMap<String, String>, // a mapping of monomorphic functions to their polymorphic counterpart
    mono_fn_ty_map: HashMap<String, Ty>,       // map of all monomorphic function types
}

impl Monomorphizer {
    pub fn new(prog: &lir::Program) -> Monomorphizer {
        let poly_fn_map = prog
            .poly_fn_map
            .iter()
            .map(|(n, i)| (n.clone(), prog.funcs[*i].clone()))
            .collect();

        let name_set = prog.funcs.iter().map(|f| f.name.clone()).collect();
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

    pub fn monomorphize(&mut self, entry: &mut lir::Func) -> Vec<lir::Func> {
        let mut poly_refs = vec![];
        self.collect(entry, &mut poly_refs);
        let mut funcs = vec![];
        for mut poly_ref in poly_refs {
            log::debug!("[monomorphize] {:?}", poly_ref);
            self.monomorphize_func(&mut poly_ref, &mut funcs);
        }
        funcs
    }

    fn add_mono_fn_mapping(&mut self, poly_name: &String, mono_name: &String) {
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

    fn monomorphize_func(
        &mut self,
        poly_ref: &mut PolyFnRef<'_>,
        funcs: &mut Vec<lir::Func>,
    ) -> (String, String) {
        // NOTE: unless there's a bug in the compiler, the callee function type is always monomorphic
        // Function types that make it here are either contained in a pure-monomorphic
        // function, which means that the call will have a concrete type, or
        // the type is contained in a monomorphized polymorphic function in which case
        // the function type has been monomorphized previously

        // check that the callee function type is monomorphic
        if poly_ref.callee_ty.is_polymorphic() {
            panic!("cannot monomorphize function where the callee type is polymorphic");
        }

        // get the polymorphic name
        let name = poly_ref.value.get_name().clone();
        let poly_fqn = Path::from(name.clone());
        let poly_base_name = poly_fqn.to_string();
        let poly_name = sema::fn_name(&poly_base_name, &poly_ref.poly_ty);

        // get the monomorphized name using a substitution
        let subst = poly_ref
            .poly_ty
            .mgu(&poly_ref.callee_ty)
            .ok()
            .unwrap_or_default();
        log::debug!("[monomorphize] subst = {:#?}", subst);
        let mono_fqn = poly_fqn.clone().apply_subst(&subst);
        let mono_base_name = mono_fqn.to_string();
        let mono_name = if self.name_set.contains(&mono_base_name) {
            mono_base_name.clone()
        } else {
            sema::fn_name(&mono_base_name, &poly_ref.callee_ty)
        };

        log::debug!("[monomorphize] poly_name = {}", poly_name);
        log::debug!("[monomorphize] mono_name = {}", mono_name);

        // set the name
        poly_ref.value.set_name(mono_name.clone());

        // make sure that the functions are not externs
        if self.extern_set.contains(&poly_base_name) || self.extern_set.contains(&mono_base_name) {
            return (poly_base_name, mono_base_name);
        }

        // add it to the map
        self.mono_poly_fn_idx
            .insert(poly_name.clone(), mono_name.clone());

        // make sure that there isn't already a monomorphized version
        if self.mono_fn_ty_map.contains_key(&mono_name) {
            return (poly_name, mono_name);
        }

        // get the polymorphic function from the index and add a mapping from poly to mono
        let mut mono_fn = self
            .poly_fn_map
            .get(&name)
            .cloned()
            .expect(&format!("polymorphic function `{}` is undefined", name));
        mono_fn.name = mono_name.clone();
        mono_fn.ty = poly_ref.callee_ty.clone();

        self.add_mono_fn_mapping(&poly_name, &mono_name);

        // apply the substitution to the function
        mono_fn = mono_fn.apply_subst(&subst);

        // collect further polymorphic functions from the new monomorphized function
        let mut poly_refs = vec![];
        let mut symbols = mono_fn.symbols.clone();
        self.collect(&mut mono_fn, &mut poly_refs);

        for mut poly_ref in poly_refs {
            let (poly_name, mono_name) = self.monomorphize_func(&mut poly_ref, funcs);
            log::debug!("symbols: {:?}", symbols);
            log::debug!("poly_name: {}", poly_name);
            log::debug!("mono_name: {}", mono_name);
            symbols.remove(&poly_name);
            symbols.insert(mono_name);
        }

        mono_fn.symbols = symbols;
        funcs.push(mono_fn);
        (poly_name, mono_name)
    }

    fn collect<'a, T>(&self, insts: T, poly_refs: &mut Vec<PolyFnRef<'a>>)
    where
        T: IntoIterator<Item = &'a mut Node<lir::Inst, SourceInfo>>,
    {
        for inst in insts.into_iter() {
            log::debug!("[monomorphize] collect: {}", inst);
            match &mut inst.value {
                lir::Inst::Value(v)
                | lir::Inst::SetGlobal(_, v)
                | lir::Inst::SetLocal(_, v)
                | lir::Inst::IncRef(v, _)
                | lir::Inst::DecRef(v)
                | lir::Inst::Return(v) => self.add_ref_from_value(v, poly_refs),
                lir::Inst::Store(s) => self.add_ref_from_value(&mut s.value, poly_refs),
                _ => continue,
            }
        }
    }

    fn add_ref_from_value<'a>(
        &self,
        value: &'a mut lir::Value,
        poly_refs: &mut Vec<PolyFnRef<'a>>,
    ) {
        let (callee_ty, poly_ty, path) = match value {
            lir::Value::Atom(a) => match a {
                lir::Atom::FuncRef(_) => todo!(),
                _ => return,
            },
            lir::Value::Call(c) => {
                if c.fn_ref.is_some() {
                    return;
                }

                let poly_ty = match &c.poly_ty {
                    Some(t) => t.clone(),
                    _ => return,
                };

                (c.ty.clone(), poly_ty, Path::from(c.fn_name.as_str()))
            }
            lir::Value::CExternCall(_) => todo!(),
            _ => return,
        };

        // self.add_ref(poly_refs, value, path, ty, poly_ty);
        poly_refs.push(PolyFnRef {
            value,
            path,
            poly_ty,
            callee_ty,
        });
    }

    // fn add_ref<'a>(
    //     &self,
    //     poly_refs: &mut Vec<PolyFnRef<'a>>,
    //     value: &'a mut lir::Value,
    //     path: Path,
    //     callee_ty: Ty,
    //     poly_ty: Option<Ty>,
    // ) {
    //     // let mut poly_ty = callee_ty.clone();
    //     // log::debug!("[monomorphize] add_ref - ty = {}", poly_ty);

    //     // let mut tf = TyVarFactory::scoped("*", path.clone());
    //     // let mut subst = HashMap::new();
    //     // poly_ty = poly_ty.polymorphize(&mut tf, &mut subst);
    //     // log::debug!("[monomorphize] polymorphized ty = {}", poly_ty);

    //     // let subst = poly_ty.formalize();
    //     // poly_ty = poly_ty.apply_subst(&subst);
    //     // log::debug!("[monomorphize] formalized polymorphized ty = {}", poly_ty);

    //     poly_refs.push(PolyFnRef {
    //         value,
    //         path,
    //         poly_ty,
    //         callee_ty,
    //     });
    // }
}
