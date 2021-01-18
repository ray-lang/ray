use std::collections::HashMap;

use crate::{
    ast::Path,
    lir, sema,
    typing::{
        top::{state::TyVarFactory, traits::Polymorphize},
        ApplySubst,
    },
};

#[derive(Debug)]
pub struct Monomorphizer<'a> {
    prog: &'a lir::Program,
    poly_fn_idx: HashMap<String, usize>, // polymorphic functions
    poly_mono_fn_idx: HashMap<String, Vec<String>>, // a mapping of polymorphic functions to monomorphizations
    mono_poly_fn_idx: HashMap<String, String>, // a mapping of monomorphic functions to their polymorphic counterpart
    mono_fn_ty_map: HashMap<String, lir::FnType>, // map of all monomorphic function types
}

impl Monomorphizer<'_> {
    pub fn new(prog: &lir::Program) -> Monomorphizer<'_> {
        Monomorphizer {
            prog,
            poly_fn_idx: HashMap::new(),
            poly_mono_fn_idx: HashMap::new(),
            mono_poly_fn_idx: HashMap::new(),
            mono_fn_ty_map: HashMap::new(),
        }
    }

    pub fn monomorphize(&mut self) -> Vec<lir::Func> {
        let refs = self.prog.poly_fn_refs.clone();
        refs.into_iter()
            .flat_map(|poly_ref| {
                log::debug!("[monomorphize] {:?}", poly_ref);
                self.monomorphize_func(&poly_ref)
            })
            .collect()
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

    fn monomorphize_func(&mut self, poly_ref: &lir::PolyFnRef) -> Vec<lir::Func> {
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
        let poly_fqn = Path::from(poly_ref.name.clone());
        let poly_name = poly_fqn.to_string();

        // make sure that the poly function is not an extern
        if self.prog.extern_set.contains(&poly_name) {
            return vec![];
        }

        // get the monomorphized name using a substitution
        let subst = poly_ref
            .poly_ty
            .to_ty()
            .mgu(&poly_ref.callee_ty.to_ty())
            .ok()
            .unwrap_or_default();
        let mono_fqn = poly_fqn.clone().apply_subst(&subst);
        let mono_name = mono_fqn.to_string();

        // make sure that the mono function is not an extern
        if self.prog.extern_set.contains(&mono_name) {
            return vec![];
        }

        // add it to the map
        log::debug!("[monomorphize] poly_name = {}", poly_name);
        log::debug!("[monomorphize] mono_name = {}", mono_name);
        self.mono_poly_fn_idx
            .insert(poly_name.clone(), mono_name.clone());

        // make sure that there isn't already a monomorphized version
        if self.mono_fn_ty_map.contains_key(&mono_name) {
            return vec![];
        }

        // get the polymorphic function from the index
        let poly_fn_idx = self
            .poly_fn_idx
            .get(&poly_ref.name)
            .copied()
            .expect(&format!(
                "polymorphic function `{}` is undefined",
                poly_ref.name
            ));

        // clone the polymorphic function, add a mapping from poly to mono
        let mut mono_fn = self.prog.funcs[poly_fn_idx].clone();
        mono_fn.ty = poly_ref.callee_ty.clone();

        self.add_mono_fn_mapping(&poly_name, &mono_name);

        // create a substitution with the type parameters and the concrete types
        let poly_ty = poly_ref.poly_ty.to_ty();
        let callee_ty = poly_ref.callee_ty.to_ty();
        let sub = poly_ty.mgu(&callee_ty).ok().unwrap_or_default();

        // apply the substitution to the function
        mono_fn = mono_fn.apply_subst(&sub);

        // collect further polymorphic functions from the new monomorphized function
        let mut coll = PolyFnCollector {
            func: &mono_fn,
            poly_refs: vec![],
        };
        coll.collect();

        let poly_refs = coll.poly_refs;
        let mut funcs = vec![mono_fn];
        for poly_ref in poly_refs {
            funcs.extend(self.monomorphize_func(&poly_ref));
        }

        funcs
    }
}

struct PolyFnCollector<'a> {
    func: &'a lir::Func,
    poly_refs: Vec<lir::PolyFnRef>,
}

impl PolyFnCollector<'_> {
    fn collect(&mut self) {
        for inst in lir::InstIter::from(self.func) {
            let v = match &inst.kind {
                lir::InstKind::Value(v)
                | lir::InstKind::SetGlobal(_, v)
                | lir::InstKind::SetLocal(_, v)
                | lir::InstKind::IncRef(v, _)
                | lir::InstKind::DecRef(v)
                | lir::InstKind::Return(v) => v,
                lir::InstKind::Store(s) => &s.value,
                _ => continue,
            };

            match v {
                lir::Value::Atom(a) => match a {
                    lir::Atom::FuncRef(_) => todo!(),
                    _ => (),
                },
                lir::Value::Call(c) => {
                    if c.fn_ref.is_some() {
                        continue;
                    }
                    self.add_ref(c.original_fn.clone(), c.ty.clone());
                }
                lir::Value::CExternCall(_) => todo!(),
                _ => (),
            }
        }
    }

    fn add_ref(&mut self, name: String, callee_ty: lir::FnType) {
        let mut poly_ty = callee_ty.to_ty();
        let mut tf = TyVarFactory::new("*");
        let mut subst = HashMap::new();
        poly_ty = poly_ty.polymorphize(&mut tf, &mut subst);
        log::debug!("[monomorphize] polymorphized ty = {}", poly_ty);

        let subst = poly_ty.formalize();
        poly_ty = poly_ty.apply_subst(&subst);
        let tyvars = poly_ty.collect_tyvars();
        poly_ty = poly_ty.quantify(tyvars);
        log::debug!("[monomorphize] formalized polymorphized ty = {}", poly_ty);

        self.poly_refs.push(lir::PolyFnRef {
            name,
            poly_ty: lir::FnType::from(poly_ty),
            callee_ty: lir::FnType::from(callee_ty),
        });
    }
}
