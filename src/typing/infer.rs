use std::{
    collections::{HashMap, HashSet},
    marker::PhantomData,
};

use crate::{
    errors::RayResult,
    hir::{HirNode, HirNodeKind, Param, TypedHirNode},
    utils::join,
};

use super::{
    constraint::ConstraintSet,
    context::Ctx,
    elim::Elim,
    generalize::Generalize,
    subst::{ApplySubst, Subst},
    ty::{Ty, TyVar},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferError<T> {
    pub msg: String,
    pub metadata: Option<T>,
}

pub type InferResult<T> = Result<(TypedHirNode<T>, Ctx), InferError<T>>;

#[derive(Clone, Debug)]
pub struct InferSystem<T: Copy + Clone> {
    ctx: Ctx,
    phantom: PhantomData<T>,
}

impl<T: std::fmt::Debug + Copy + Clone> InferSystem<T> {
    pub fn new(ctx: Ctx) -> InferSystem<T> {
        InferSystem {
            ctx,
            phantom: PhantomData,
        }
    }

    fn unify(&self, a: &Ty, b: &Ty, metadata: Option<T>) -> Result<Subst, InferError<T>> {
        println!("unify: {} and {}", a, b);
        Ok(match (a, b) {
            (_, Ty::Any) | (_, Ty::Never) => Subst::new(),
            (Ty::IntLiteral, t) | (t, Ty::IntLiteral) if t.is_int_ty() => Subst::new(),
            (Ty::FloatLiteral, t) | (t, Ty::FloatLiteral) if t.is_float_ty() => Subst::new(),
            (Ty::Var(tv), t) | (t, Ty::Var(tv)) if a != b => {
                if !t.free_vars().contains(&tv) {
                    subst! { tv.clone() => t.clone() }
                } else {
                    return Err(InferError {
                        msg: format!("recursive unification: {} and {}", a, b),
                        metadata,
                    });
                }
            }
            (Ty::Projection(a, s), Ty::Projection(b, t)) if a == b => {
                let mut sub = Subst::new();
                for (x, y) in s.iter().zip(t.iter()) {
                    sub = sub.union(self.unify(x, y, metadata)?)
                }
                sub
            }
            (Ty::Func(r, s), Ty::Func(t, u)) if r.len() == t.len() => {
                let mut sub = Subst::new();
                for (x, y) in r.iter().zip(t.iter()) {
                    sub = sub.union(self.unify(x, y, metadata)?)
                }

                sub.union(self.unify(s, u, metadata)?)
            }
            (Ty::All(xs, s), Ty::All(ys, t)) if xs.len() == ys.len() => {
                self.unify(s, t, metadata)?
            }
            (Ty::All(_, s), t) => self.unify(s, t, metadata)?,
            (s, Ty::All(_, t)) => self.unify(s, t, metadata)?,
            _ => {
                return Err(InferError {
                    msg: format!("type mismatch `{}` and `{}`", a, b),
                    metadata,
                })
            }
        })
    }

    /// An [X]/V -constraint set C has the form:
    ///     { S[i] <: X[i] <: T[i] | (FV(S[i]) ∪ FV(T[i])) ∩ ({V} ∪ {X}) = ∅ }
    ///
    /// Given a set of type variables V, a set of unknowns X,
    /// and two types S and T, calculates the minimal (i.e., least constraining)
    /// X/V - constraint set C that guarantees S <: T
    // pub fn cg(
    //     &self,
    //     ty_vars: &HashSet<&TyVar>,
    //     unknowns: &HashSet<TyVar>,
    //     a: &Ty,
    //     b: &Ty,
    //     metadata: Option<T>,
    // ) -> Result<ConstraintSet, InferError<T>> {
    //     println!("cg: {:?} and {:?}", a, b);
    //     println!("  ty_vars = {:?}", ty_vars);
    //     println!("  unknowns = {:?}", unknowns);
    //     Ok(match (a, b) {
    //         (_, Ty::Any) | (Ty::Never, _) => ConstraintSet::new(),
    //         (Ty::IntLiteral, b) if b.is_int_ty() => ConstraintSet::new(),
    //         (Ty::FloatLiteral, b) if b.is_float_ty() => ConstraintSet::new(),
    //         (Ty::Var(y), _)
    //             // Y ∈ [X] && FV(S) ∩ {X} = ∅
    //             if a != b && unknowns.contains(&y) && b.free_vars().intersection(&unknowns.iter().collect()).count() == 0 => {
    //             cset! {
    //                 y => (Ty::Never) <: b.clone().elim_down(&ty_vars)?
    //             }
    //         }
    //         (_, Ty::Var(y))
    //             // Y ∈ [X] && FV(S) ∩ {X} = ∅
    //             if a != b && unknowns.contains(&y) && a.free_vars().intersection(&unknowns.iter().collect()).count() == 0 => {
    //                cset! {
    //                    y => (a.clone().elim_up(&ty_vars)?) <: Ty::Any
    //                }
    //             }
    //         (Ty::Var(y), _) | (_, Ty::Var(y)) if a == b && !unknowns.contains(&y) => { // Y ∈/ X
    //             ConstraintSet::new()
    //         }
    //         (Ty::Projection(a, s), Ty::Projection(b, t)) if a == b => {
    //             let mut c = cset!{};
    //             for (i, j) in s.iter().zip(t.iter()) {
    //                 let d = self.cg(ty_vars, unknowns, i, j, metadata)?;
    //                 c = c.meet(d);
    //             }
    //             c
    //         }
    //         (Ty::Func(r, s), Ty::Func(t, u)) if r.len() == t.len() => {
    //             // V' ⊢[X] ([T] <: [R]) ⇒ C
    //             let mut c = cset!{};
    //             for (i, j) in r.iter().zip(t.iter()) {
    //                 let d = self.cg(ty_vars, unknowns, i, j, metadata)?;
    //                 c = c.meet(d);
    //             }

    //             // V' ⊢[X] (S <: U) ⇒ D
    //             let d = self.cg(ty_vars, unknowns, s, u, metadata)?;
    //             c.meet(d)
    //         }
    //         (Ty::All(a_ys, s), Ty::All(b_ys, t))
    //             // Y ∩ (V ∪ X)= ∅
    //             if a_ys == b_ys  =>
    //         {
    //             let ys: HashSet<&TyVar> = a_ys.into_iter().collect();
    //             let x_prime: HashSet<&TyVar> = ty_vars.union(&unknowns.iter().collect()).map(|v| *v).collect();
    //             let y_intersect: HashSet<&TyVar> = ys.intersection(&x_prime).map(|v| *v).collect();
    //             if y_intersect.len() != 0 {
    //                 return Err(InferError {
    //                     msg: format!("{:?} ∩ {:?} != ∅", ys, x_prime),
    //                     metadata,
    //                 });
    //             }

    //             // V' = V ∪ {Y}
    //             let v_prime = ty_vars.union(&ys).map(|t| *t).collect();
    //             self.cg(&v_prime, &unknowns, s, t, metadata)?
    //         }
    //         (Ty::All(ys, s), t) => {
    //             let ys: HashSet<&TyVar> = ys.into_iter().collect();
    //             let x_prime: HashSet<&TyVar> = ty_vars.union(&unknowns.iter().collect()).map(|v| *v).collect();
    //             let y_intersect: HashSet<&TyVar> = ys.intersection(&x_prime).map(|v| *v).collect();
    //             if y_intersect.len() != 0 {
    //                 return Err(InferError {
    //                     msg: format!("{:?} ∩ {:?} != ∅", ys, x_prime),
    //                     metadata,
    //                 });
    //             }

    //             // V' = V ∪ {Y}
    //             let v_prime = ty_vars.union(&ys).map(|t| *t).collect();
    //             self.cg(&v_prime, unknowns, s, t, metadata)?
    //         }
    //         (s, Ty::All(ys, t)) => {
    //             let ys: HashSet<&TyVar> = ys.into_iter().collect();
    //             let x_prime: HashSet<&TyVar> = ty_vars.union(&unknowns.iter().collect()).map(|v| *v).collect();
    //             let y_intersect: HashSet<&TyVar> = ys.intersection(&x_prime).map(|v| *v).collect();
    //             if y_intersect.len() != 0 {
    //                 return Err(InferError {
    //                     msg: format!("{:?} ∩ {:?} != ∅", ys, x_prime),
    //                     metadata,
    //                 });
    //             }

    //             // V' = V ∪ {Y}
    //             let v_prime = ty_vars.union(&ys).map(|t| *t).collect();
    //             self.cg(&v_prime, unknowns, s, t, metadata)?
    //         }
    //         _ => return Err(InferError {
    //             msg: format!("types `{}` and `{}` cannot be unified", a, b),
    //             metadata
    //         }),
    //     })
    // }

    fn unify_fn_args(
        &self,
        args: Vec<HirNode<T>>,
        param_tys: &Vec<Ty>,
        unknowns: &HashSet<TyVar>,
    ) -> Result<(Vec<HirNode<T>>, Ctx), InferError<T>> {
        let mut typed_args = vec![];
        let mut ctx = Ctx::new();
        for (arg, param_ty) in args.into_iter().zip(param_tys.iter()) {
            // first infer the types of the argument
            let (mut arg, arg_ctx) = self.infer_ty(arg)?;
            ctx.subst = ctx.subst.union(arg_ctx.subst);

            // if this is a unification variable
            let mut arg_ty = arg.get_type();
            println!("arg_ty: {}", arg_ty);
            match arg_ty {
                Ty::Var(tv) if !unknowns.contains(&tv) && !arg_ty.is_tyvar() => {
                    // then apply the substitution to the param type and
                    // use that instead of the variable
                    println!("param_ty: {}", param_ty);
                    arg_ty = param_ty.clone().apply_subst(&ctx.subst);
                    println!("arg_ty: {}", arg_ty);
                    println!("tv: {}", tv);
                    ctx.subst.insert(tv, arg_ty.clone());
                    arg.set_type(arg_ty);
                }
                _ => {
                    // then we create set of constraints using the argument
                    // and parameter types: ∅ ⊢X S <: T ⇒ D
                    let s = self.unify(&arg_ty, param_ty, arg.get_metadata())?;
                    ctx.subst = ctx.subst.union(s);
                }
            }

            typed_args.push(HirNode::typed(arg));
        }

        Ok((typed_args, ctx))
    }

    fn infer_var(&self, v: String, metadata: Option<T>) -> InferResult<T> {
        let mut rev_sub = HashMap::new();
        let ty = match self.ctx.try_get_var(&v, metadata)? {
            Ty::Union(mut tys) if tys.len() == 1 => tys.pop().unwrap(),
            Ty::Union(mut tys) if tys.len() > 1 => {
                let ty = tys.pop().unwrap();
                let ty = tys
                    .into_iter()
                    .fold(ty, |t, x| t.generalize(x, &mut rev_sub));

                // let ty = if let Ty::All(xs, t) = t {
                //     (xs, *t.clone())
                // } else {
                //     (vec![], t)
                // };

                let ty = ty
                    .clone()
                    .constrain_for(v.clone(), ty)
                    .close(&self.ctx.free_vars());
                println!("constrained: {}", ty);
                ty
            }
            t => t,
        };

        println!("infer_var: {} = {}", v, ty);

        Ok((
            TypedHirNode::new(
                HirNode {
                    kind: HirNodeKind::Var(v),
                    metadata,
                },
                ty,
            ),
            Ctx::new(),
        ))
    }

    fn infer_let(
        &self,
        vars: Vec<(String, HirNode<T>)>,
        body: HirNode<T>,
        metadata: Option<T>,
    ) -> InferResult<T> {
        let mut typed_vars: Vec<(String, HirNode<T>)> = vec![];
        let mut infer = self.clone();
        for (name, rhs) in vars {
            let (typed_rhs, _) = match rhs.kind {
                HirNodeKind::FunInf(xs, mut params, fn_body) => {
                    // we can't infer the type of a function on the RHS
                    // until we infer the type of the body, but we'll need to
                    // create a function with unknown variables first

                    // create parameter types using type variables
                    for p in params.iter_mut() {
                        let ty = p.get_ty_mut();
                        *ty = Some(Ty::Var(TyVar::new()));
                    }

                    // let body_metadata = body.metadata;
                    // let rhs_metadata = rhs.metadata;
                    infer.infer_fn(xs, params, *fn_body, rhs.metadata)?
                }
                _ => {
                    // first, infer the type of the RHS
                    infer.infer_ty(rhs)?
                }
            };

            // with the function type create another context with the bound variable
            infer = infer.clone();
            infer.ctx.bind_var(name.clone(), typed_rhs.get_type());

            if let Some((n, x)) = typed_vars.pop() {
                let x = x.apply_subst(&infer.ctx.subst);
                infer.ctx.bind_var(n.clone(), x.get_type());
                typed_vars.push((n, x));
            }

            typed_vars.push((name, HirNode::typed(typed_rhs)));
        }

        // using the new context infer the type of the body
        let (body, mut body_ctx) = infer.infer_ty(body)?;
        let ty = body.get_type();
        body_ctx.subst = body_ctx.subst.union(infer.ctx.subst);

        if let Some((n, x)) = typed_vars.pop() {
            let x = x.apply_subst(&body_ctx.subst);
            body_ctx.bind_var(n.clone(), x.get_type());
            typed_vars.push((n, x));
        }

        Ok((
            TypedHirNode::new(
                HirNode {
                    kind: HirNodeKind::Let(typed_vars, Box::new(HirNode::typed(body))),
                    metadata,
                },
                ty,
            ),
            body_ctx,
        ))
    }

    pub fn infer_fn(
        &self,
        xs: Vec<TyVar>,
        mut params: Vec<Param<T>>,
        body: HirNode<T>,
        metadata: Option<T>,
    ) -> InferResult<T> {
        let mut infer = self.clone();
        let mut param_tys = vec![];
        for param in params.iter() {
            let param_ty = param.get_ty().unwrap().clone();
            param_tys.push(param_ty.clone());
            infer.ctx.bind_var(param.get_name().clone(), param_ty);
        }
        for tv in xs.iter().cloned() {
            infer.ctx.add_ty_var(tv);
        }

        let (body, body_ctx) = infer.infer_ty(body)?;
        let mut new_param_tys = vec![];
        for param in params.iter_mut() {
            let ty = param.get_ty_mut().as_mut().unwrap();
            *ty = ty.clone().apply_subst(&body_ctx.subst);
            new_param_tys.push(ty.clone());
        }

        let mut fn_ty = Ty::Func(new_param_tys, Box::new(body.get_type()));
        if xs.len() != 0 {
            fn_ty = Ty::All(xs.clone(), Box::new(fn_ty));
        }

        Ok((
            TypedHirNode::new(
                HirNode {
                    kind: HirNodeKind::Fun(xs, params, Box::new(HirNode::typed(body))),
                    metadata,
                },
                fn_ty,
            ),
            body_ctx,
        ))
    }

    fn sat_set(
        &self,
        unknowns: &HashSet<TyVar>,
        constraints: Vec<(String, Ty)>,
        metadata: Option<T>,
    ) -> Result<Option<Subst>, InferError<T>> {
        println!(
            "sat_set: unknowns = {:?}, constraints = {:?}",
            unknowns, constraints
        );
        if constraints.len() == 0 {
            return Ok(Some(Subst::new()));
        }

        let sets = self.sat_sets(unknowns, constraints.clone(), vec![], metadata)?;
        if sets.len() == 0 {
            return Ok(None);
        }

        let mut subst = subst!();
        for (_, ty) in constraints {
            let mut ty_primes = sets
                .iter()
                .map(|sub| ty.clone().apply_subst(sub))
                .collect::<Vec<Ty>>();

            let mut reverse_subst = HashMap::new();
            let ty_prime = ty_primes.remove(0);
            let ty_prime = ty_primes
                .into_iter()
                .fold(ty_prime, |t, s| t.generalize(s, &mut reverse_subst));

            println!("ty_prime = {:?}", ty_prime);
            subst = match self.unify(&ty, &ty_prime, metadata) {
                Ok(s) => subst.union(s),
                Err(_) => continue,
            }
        }

        Ok(Some(Subst::new()))
    }

    fn sat_sets(
        &self,
        unknowns: &HashSet<TyVar>,
        mut k: Vec<(String, Ty)>,
        k0: Vec<(String, Ty)>,
        metadata: Option<T>,
    ) -> Result<Vec<Subst>, InferError<T>> {
        if k.len() == 0 {
            return Ok(vec![Subst::new()]);
        }

        let (o, t) = k.remove(0);
        if k0.contains(&(o.clone(), t.clone())) {
            return self.sat_sets(unknowns, k, k0, metadata);
        }

        let mut sets = vec![];
        if let Some(t_prime) = self.ctx.get_var(&o) {
            let t_primes = if let Ty::Union(t_primes) = t_prime {
                t_primes.iter().collect()
            } else {
                vec![t_prime]
            };

            for t_prime in t_primes {
                let (xs, k_prime, t_prime) = t_prime.clone().unpack_constrained();
                let k_prime = k_prime.unwrap_or_default();
                let mut unknowns = unknowns.clone();
                unknowns.extend(xs.unwrap_or_default().into_iter());
                println!("t = {:?}", t);
                println!("t_prime = {:?}", t_prime);
                println!("unknowns = {:?}", unknowns);
                let sub = match self.unify(&t, &t_prime, metadata) {
                    Ok(sub) => sub,
                    _ => continue,
                };

                let t_sub = t.clone().apply_subst(&sub);
                let mut k0_prime = k0.clone();
                k0_prime.push((o.clone(), t_sub));

                let ks = match self.sat_sets(
                    &unknowns,
                    k_prime.apply_subst(&sub),
                    k0_prime.clone(),
                    metadata,
                ) {
                    Ok(ks) => ks,
                    _ => continue,
                };

                if ks.len() != 0 {
                    let s_prime = match self.sat_sets(
                        &unknowns,
                        k.clone().apply_subst(&sub),
                        k0_prime,
                        metadata,
                    ) {
                        Ok(s_prime) => s_prime,
                        _ => continue,
                    };
                    sets.extend(s_prime.into_iter().map(|s| s.union(sub.clone())));
                }
            }
        }

        Ok(sets)
    }

    fn infer_type_arguments(
        &self,
        f: &TypedHirNode<T>,
        ty_params: &Option<Vec<TyVar>>,
        args: Vec<HirNode<T>>,
        param_tys: &Vec<Ty>,
        ret_ty: &Ty,
        unknowns: &HashSet<TyVar>,
    ) -> Result<(Vec<HirNode<T>>, Ctx), InferError<T>> {
        // for each of the param types, if there are any unification
        // variables, the need to be added to the set of unknowns
        let (typed_args, mut ctx) = self.unify_fn_args(args, param_tys, unknowns)?;

        // if let Some(ty_params) = ty_params {
        //     // apply the substitution to the type parameters
        //     for ty_param in ty_params.iter() {
        //         if ctx.subst.get(ty_param).is_none() {
        //             return Err(InferError {
        //                 msg: format!(
        //                     "cannot determine argument for type parameter {} for expression {} (substitution = {:#?})",
        //                     ty_param, f, ctx.subst
        //                 ),
        //                 metadata: f.get_expr().metadata,
        //             });
        //         }
        //     }
        // }

        Ok((typed_args, ctx))
    }

    fn infer_fn_arguments(
        &self,
        ty_params: &Option<Vec<TyVar>>,
        ty_args: &Vec<Ty>,
        args: Vec<HirNode<T>>,
        param_tys: &Vec<Ty>,
    ) -> Result<(Vec<HirNode<T>>, Ctx), InferError<T>> {
        let mut ctx = Ctx::new();
        if let Some(ty_params) = &ty_params {
            ctx.subst = ctx
                .subst
                .union(Subst::from_types(ty_params.clone(), ty_args.clone()))
        }

        // for each parameter type in the function, check the arguments
        let mut typed_args = vec![];
        for (mut arg, param_ty) in args.into_iter().zip(param_tys.iter()) {
            let mut arg_ty = param_ty.clone().apply_subst(&ctx.subst);

            // if this is a unification variable
            if let Ty::Var(tv) = arg_ty {
                // then infer the type and add it to the substitution
                let (typed_arg, arg_ctx) = self.infer_ty(arg)?;
                let ty = typed_arg.get_type();
                ctx.subst.insert(tv, ty.clone());
                ctx.subst = ctx.subst.union(arg_ctx.subst);
                arg = HirNode::typed(typed_arg);
                arg_ty = ty;
            }

            let (arg, arg_ctx) = self.check_ty(arg, arg_ty)?;
            ctx.subst = ctx.subst.union(arg_ctx.subst);
            typed_args.push(HirNode::typed(arg));
        }

        Ok((typed_args, ctx))
    }

    pub fn infer_apply(
        &self,
        f: HirNode<T>,
        ty_args: Vec<Ty>,
        args: Vec<HirNode<T>>,
        metadata: Option<T>,
    ) -> InferResult<T> {
        let (mut fn_ex, _) = self.infer_ty(f)?;

        let fn_ty = fn_ex.get_type();
        let fn_types = fn_ty.try_unpack_overloaded_fn()?;

        let mut errs = vec![];
        let mut options = vec![];
        let sys = self.clone();
        for fn_ty in fn_types {
            let unknowns = fn_ty.collect_tyvars();
            let (ty_params, mut constraints, param_tys, ret_ty) = fn_ty.try_unpack_fn()?;
            if let Some(ty_params) = &ty_params {
                if ty_args.len() != 0 && ty_args.len() != 0 && ty_args.len() != ty_params.len() {
                    // does not check since we have a different number of type arguments to type parameters
                    // according to the local type inference specification this is considered an error
                    errs.push(InferError {
                        msg: format!(
                            "cannot infer types of missing type arguments for {:#?}",
                            fn_ex
                        ),
                        metadata,
                    });
                    continue;
                }
            }

            if param_tys.len() != args.len() {
                continue;
            }

            let args = args.clone();
            let infer_result = if matches!(&ty_params, Some(v) if v.len() != 0 && ty_args.len() == 0)
            {
                // if the function is defined with type parameters, but the
                // application does not provide type arguments we need to infer them
                sys.infer_type_arguments(&fn_ex, &ty_params, args, &param_tys, &ret_ty, &unknowns)
            } else {
                // either there are no type parameters/arguments or all
                // type arguments are provided
                // create a substitution mapping the type parameters to the type arguments
                sys.infer_fn_arguments(&ty_params, &ty_args, args, &param_tys)
            };

            let (typed_args, ctx) = match infer_result {
                Ok((t, c)) => (t, c),
                Err(e) => {
                    errs.push(e);
                    continue;
                }
            };

            println!("subst = {:?}", ctx.subst);

            let arg_constraints = typed_args
                .iter()
                .flat_map(|a| a.get_type().get_constraints())
                .collect::<Vec<_>>();

            constraints.extend(arg_constraints);

            // now we infer the type of the return by applying the substitution
            let param_tys = param_tys.apply_subst(&ctx.subst);
            let ret_ty = ret_ty.apply_subst(&ctx.subst);
            let fn_ty = Ty::Func(param_tys, Box::new(ret_ty.clone()));
            let fn_ty = if let Some(ty_params) = ty_params {
                Ty::All(ty_params, Box::new(fn_ty))
            } else {
                fn_ty
            };

            constraints = constraints.apply_subst(&ctx.subst);
            println!("constraints: {:?}", constraints);
            println!("typed_args: {:?}", typed_args);
            println!("ret_ty: {:?}", ret_ty);
            println!("fn_ty: {:?}", fn_ty);

            if let Some(sub) = self.sat_set(&unknowns, constraints.clone(), metadata)? {
                if !sub.is_empty() {
                    continue;
                }
                options.push((typed_args, ret_ty, fn_ty, ctx));
            }
        }

        if options.len() == 1 {
            let (typed_args, ret_ty, fn_ty, ctx) = options.pop().unwrap();
            fn_ex.set_type(fn_ty);
            let typed_fn = HirNode::typed(fn_ex);
            Ok((
                TypedHirNode::new(
                    HirNode {
                        kind: HirNodeKind::Apply(Box::new(typed_fn), ty_args, typed_args),
                        metadata,
                    },
                    ret_ty,
                ),
                ctx,
            ))
        } else if options.len() == 0 {
            if errs.len() != 0 {
                Err(errs.remove(0))
            } else {
                Err(InferError {
                    msg: format!("cannot find overload"),
                    metadata,
                })
            }
        } else {
            Err(InferError {
                msg: format!("ambiguous reference to overloaded function"),
                metadata,
            })
        }
    }

    pub fn infer_ty(&self, ex: HirNode<T>) -> InferResult<T> {
        match ex.kind {
            HirNodeKind::Const(t) => Ok((
                TypedHirNode::new(
                    HirNode {
                        kind: HirNodeKind::Const(t.clone()),
                        metadata: ex.metadata,
                    },
                    t,
                ),
                Ctx::new(),
            )),
            HirNodeKind::Struct(n, els) => {
                let mut typed_els = vec![];
                let mut el_tys = vec![];
                let mut ctx = self.ctx.clone();
                for (el_name, el) in els.into_iter() {
                    let (el, c) = self.infer_ty(el)?;
                    ctx.subst = ctx.subst.union(c.subst);
                    let typed_el = HirNode::typed(el);
                    el_tys.push(typed_el.get_type());
                    typed_els.push((el_name, typed_el));
                }
                Ok((
                    TypedHirNode::new(
                        HirNode {
                            kind: HirNodeKind::Struct(n.clone(), typed_els),
                            metadata: ex.metadata,
                        },
                        Ty::Projection(n, el_tys),
                    ),
                    ctx,
                ))
            }
            HirNodeKind::Var(v) => self.infer_var(v, ex.metadata),
            HirNodeKind::Let(vars, body) => self.infer_let(vars, *body, ex.metadata),
            HirNodeKind::Apply(f, ty_args, args) => {
                self.infer_apply(*f, ty_args, args, ex.metadata)
            }
            HirNodeKind::Fun(xs, params, body) => self.infer_fn(xs, params, *body, ex.metadata),
            HirNodeKind::FunInf(..) => Err(InferError {
                msg: format!("cannot synthesize type of unannotated function: {}", ex),
                metadata: ex.metadata,
            }),
            HirNodeKind::Typed(t) => Ok((t, Ctx::new())),
        }
    }

    fn check_apply(
        &self,
        f: HirNode<T>,
        ty_args: Vec<Ty>,
        args: Vec<HirNode<T>>,
        expected_ty: Ty,
        metadata: Option<T>,
    ) -> InferResult<T> {
        // first, infer the type of the function we are applying
        let (fn_ex, _) = self.infer_ty(f.clone())?;
        let fn_ty = fn_ex.get_type();
        let unknowns = fn_ty.collect_tyvars();
        let (ty_params, constraints, param_tys, mut ret_ty) = fn_ty.try_unpack_fn()?;
        if let Some(ty_params) = &ty_params {
            if ty_args.len() != 0 && ty_args.len() != 0 && ty_args.len() != ty_params.len() {
                // does not check since we have a different number of type arguments to type parameters
                // according to the local type inference specification this is considered an error
                return Err(InferError {
                    msg: format!("cannot check types of missing type arguments for {}", fn_ex),
                    metadata,
                });
            }
        }

        let (typed_args, ctx) = if matches!(&ty_params, Some(v) if v.len() != 0 && ty_args.len() == 0)
        {
            // type arguments are not provided so they need to be inferred
            // through constraint generation from the function arguments
            let (args, mut ctx) = self.unify_fn_args(args, &param_tys, &unknowns)?;

            // generate constraints for the return type
            let s = self.unify(&ret_ty, &expected_ty, metadata)?;
            ctx.subst = ctx.subst.union(s);

            (args, ctx)
        } else {
            // either no type parameters/arguments or all type arguments are provided
            // create a substitution mapping the type parameters to the
            // type arguments provided by the application
            let mut ctx = Ctx::new();
            if let Some(ty_params) = &ty_params {
                ctx.subst = ctx
                    .subst
                    .union(Subst::from_types(ty_params.clone(), ty_args.clone()))
            }

            // for each argument in the application, check against the
            // parameter type applied with the type arguments
            let mut new_args = vec![];
            for (arg, param_ty) in args.into_iter().zip(param_tys.iter()) {
                let arg_ty = param_ty.clone().apply_subst(&ctx.subst);
                let (arg, arg_ctx) = self.check_ty(arg, arg_ty)?;
                ctx.subst = ctx.subst.union(arg_ctx.subst);
                new_args.push(HirNode::typed(arg));
            }

            // apply the type arguments to the return type of the function
            // and then check that the applied return type is a subtype
            // of the actual result type
            ret_ty = ret_ty.apply_subst(&ctx.subst);
            if !ret_ty.is_subtype(&expected_ty) {
                return Err(InferError {
                    msg: format!(
                        "inferred return type {} is not a subtype of the actual type {}",
                        ret_ty, expected_ty
                    ),
                    metadata,
                });
            }

            (new_args, ctx)
        };

        Ok((
            TypedHirNode::new(
                HirNode {
                    kind: HirNodeKind::Apply(Box::new(f), ty_args, typed_args),
                    metadata,
                },
                ret_ty,
            ),
            ctx,
        ))
    }

    pub fn check_ty(&self, ex: HirNode<T>, expected_ty: Ty) -> InferResult<T> {
        if expected_ty == Ty::Any {
            // revert to inference mode
            return self.infer_ty(ex);
        }

        let metadata = ex.metadata;
        Ok(match ex.kind {
            HirNodeKind::Typed(t) => self.check_ty(t.take_expr(), expected_ty)?,
            HirNodeKind::Const(t) => {
                if !t.is_subtype(&expected_ty) {
                    panic!("{} is not a subtype of expected type `{}`", t, expected_ty)
                    // return Err(InferError {
                    //     msg: format!("{} is not a subtype of expected type `{}`", t, expected_ty),
                    //     metadata,
                    // });
                }

                (
                    TypedHirNode::new(
                        HirNode {
                            kind: HirNodeKind::Const(t.clone()),
                            metadata,
                        },
                        t,
                    ),
                    Ctx::new(),
                )
            }
            HirNodeKind::Struct(n, els) => {
                let (expected_name, expected_el_tys) = match expected_ty {
                    Ty::Projection(n, t) => (n, t),
                    _ => {
                        return Err(InferError {
                            msg: format!("expected a projection type, but found `{}`", expected_ty),
                            metadata,
                        })
                    }
                };

                if expected_name != n {
                    return Err(InferError {
                        msg: format!(
                            "expected projection type named `{}`, but found `{}`",
                            n, expected_name
                        ),
                        metadata,
                    });
                }

                let mut typed_els = vec![];
                let mut el_tys = vec![];
                let mut ctx = Ctx::new();
                for ((el_name, el), expected_el_ty) in
                    els.into_iter().zip(expected_el_tys.into_iter())
                {
                    let (el, c) = self.check_ty(el, expected_el_ty)?;
                    ctx.subst = ctx.subst.union(c.subst);
                    let typed_el = HirNode::typed(el);
                    el_tys.push(typed_el.get_type());
                    typed_els.push((el_name, typed_el));
                }

                (
                    TypedHirNode::new(
                        HirNode {
                            kind: HirNodeKind::Struct(n.clone(), typed_els),
                            metadata: ex.metadata,
                        },
                        Ty::Projection(n, el_tys),
                    ),
                    ctx,
                )
            }
            HirNodeKind::Var(v) => {
                let mut ty_prime = self.ctx.try_get_var(&v, metadata)?;
                if let Ty::Var(_) = ty_prime {
                    ty_prime = expected_ty;
                } else if !ty_prime.is_subtype(&expected_ty) {
                    return Err(InferError {
                        msg: format!(
                            "`{}` is not a subtype of expected type `{}`",
                            ty_prime, expected_ty
                        ),
                        metadata,
                    });
                }

                (
                    TypedHirNode::new(
                        HirNode {
                            kind: HirNodeKind::Var(v),
                            metadata,
                        },
                        ty_prime,
                    ),
                    Ctx::new(),
                )
            }
            HirNodeKind::Let(vars, body) => {
                let mut infer = self.clone();
                let mut typed_vars = vec![];
                for (name, rhs) in vars {
                    // take the first one out and infer it's type
                    let (rhs, _) = infer.infer_ty(rhs)?;

                    // in a new context bind the variable to the type
                    infer = infer.clone();
                    infer.ctx.bind_var(name.clone(), rhs.get_type());

                    typed_vars.push((name, HirNode::typed(rhs)));
                }

                // using the new context check the type of the body
                let (body, body_ctx) = infer.check_ty(*body, expected_ty)?;
                let ty = body.get_type();

                (
                    TypedHirNode::new(
                        HirNode {
                            kind: HirNodeKind::Let(typed_vars, Box::new(HirNode::typed(body))),
                            metadata,
                        },
                        ty,
                    ),
                    body_ctx,
                )
            }
            HirNodeKind::FunInf(ty_args, params, body) => {
                let (ty_params, constraints, param_tys, ret_ty) = expected_ty.try_unpack_fn()?;
                let (body, body_ctx) = self.check_ty(*body, ret_ty)?;
                let ret_ty = body.get_type();
                let fn_ty = Ty::Func(param_tys, Box::new(ret_ty));
                let ty = if let Some(ty_params) = ty_params {
                    Ty::All(ty_params, Box::new(fn_ty))
                } else {
                    fn_ty
                };

                (
                    TypedHirNode::new(
                        HirNode {
                            kind: HirNodeKind::FunInf(
                                ty_args,
                                params,
                                Box::new(HirNode::typed(body)),
                            ),
                            metadata,
                        },
                        ty,
                    ),
                    body_ctx,
                )
            }
            HirNodeKind::Fun(xs, params, body) => {
                let (xs_prime, constraints, param_tys, ret_ty) = expected_ty.try_unpack_fn()?;

                if xs_prime.as_ref().map_or(false, |xs_prime| &xs != xs_prime) {
                    return Err(InferError {
                        msg: format!(
                            "type arguments do not match [{}] and [{}]",
                            join(xs, ", "),
                            join(xs_prime.unwrap(), ", "),
                        ),
                        metadata,
                    });
                } else if xs.len() != 0 && xs_prime.is_none() {
                    return Err(InferError {
                        msg: format!(
                            "expected type arguments [{}] but found none",
                            join(xs, ", "),
                        ),
                        metadata,
                    });
                }

                for (p, p_prime) in params.iter().zip(param_tys.iter()) {
                    if p.get_ty().unwrap() == p_prime {
                        return Err(InferError {
                            msg: format!(
                                "expected type {} for {} in annotation but found {}",
                                p_prime,
                                p.get_name(),
                                p
                            ),
                            metadata: p.get_metadata(),
                        });
                    }
                }

                let (body, body_ctx) = self.check_ty(*body, ret_ty)?;
                let ret_ty = body.get_type();
                let fn_ty = Ty::Func(param_tys, Box::new(ret_ty));
                let ty = if let Some(xs_prime) = xs_prime {
                    Ty::All(xs_prime, Box::new(fn_ty))
                } else {
                    fn_ty
                };

                (
                    TypedHirNode::new(
                        HirNode {
                            kind: HirNodeKind::Fun(xs, params, Box::new(HirNode::typed(body))),
                            metadata,
                        },
                        ty,
                    ),
                    body_ctx,
                )
            }
            HirNodeKind::Apply(f, ty_args, args) => {
                self.check_apply(*f, ty_args, args, expected_ty, metadata)?
            }
        })
    }
}
