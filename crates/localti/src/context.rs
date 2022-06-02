use std::collections::{HashMap, HashSet};

use crate::{
    constraints::{gen_constraints, Constraint, ConstraintGenError, SubtypeConstraint},
    types::{TAll, TFunc, TVar, Type},
    variance::Variance,
};

#[derive(Debug, Clone)]
pub struct TypeContext {
    bounds: HashMap<TVar, Vec<Type>>,
    impls: HashMap<Type, HashSet<Type>>,
}

impl TypeContext {
    pub fn new() -> Self {
        Self {
            bounds: HashMap::new(),
            impls: HashMap::new(),
        }
    }

    pub fn infer_app(&self, f: &TAll, args: Vec<Type>) -> Result<Type, ConstraintGenError> {
        let mut tcx = self.clone();
        let vars = HashSet::new();
        let unknowns = f.tyvars.iter().map(|(v, _)| v.clone()).collect();
        let mut cs1 = HashMap::new();
        for (tv, bounds) in f.tyvars.iter() {
            let a = Type::Var(tv.clone());
            if let Some(bounds) = bounds {
                tcx.set_bounds(tv.clone(), bounds.clone());
                for b in bounds.iter() {
                    let c = gen_constraints(&tcx, &vars, &unknowns, &a, b)?;
                    cs1 = self.constraint_set_meet(cs1, c)?
                }
            }
        }

        let (params, ret_ty) = if let Type::Func(func) = f.ty.as_ref() {
            (&func.params, func.ret_ty.as_ref())
        } else {
            panic!("not a function type")
        };

        let cs2 =
                args.iter()
                    .zip(params.iter())
                    .try_fold(HashMap::new(), |c1, (a, b)| {
                        let c2 = gen_constraints(&tcx, &vars, &unknowns, a, b)?;
                        self.constraint_set_meet(c1, c2)
                    })?;

        let cs = self.constraint_set_meet(cs1, cs2)?;

        let subst = TypeContext::min_subst(ret_ty, &cs);
        // ensure the substitution satisfies the constraints
        for (tv, ty) in subst.iter() {
            if let Some(c) = cs.get(tv) {
                if let Some(err) = c.satisfies(ty, &tcx) {
                    return Err(ConstraintGenError(
                        format!("constraint is not satisfied: {}\n  {}", c, err)
                    ));
                }
            } else {
                return Err(ConstraintGenError(
                    format!("type variable {} does not have a constraint", tv)
                ));
            }
        }

        if subst.len() != 0 {
            println!("{{");
            for (k, v) in subst.iter() {
                println!("  {} :: {}", k, v);
            }
            println!("}}");
        }

        Ok(f.ty.apply_substs(&subst))
    }

    pub fn get_bounds(&self, tv: &TVar) -> Option<&Vec<Type>> {
        self.bounds.get(tv)
    }

    pub fn set_bounds(&mut self, tv: TVar, bounds: Vec<Type>) {
        self.bounds.insert(tv, bounds);
    }

    pub fn add_impl(&mut self, ty: Type, impl_ty: Type) {
        self.impls.entry(ty).or_default().insert(impl_ty);
    }

    pub fn min_subst(ty: &Type, cs: &HashMap<TVar, Constraint>) -> HashMap<TVar, Type> {
        let mut subst = HashMap::new();
        for c in cs.values() {
            let var = match c {
                Constraint::Eq(eq) => eq.var.clone(),
                Constraint::Subtype(st) => st.var.clone(),
            };

            match Type::Var(var.clone()).variance(ty) {
                Variance::Constant | Variance::Covariant => {
                    subst.insert(var, c.min_type().clone());
                }
                Variance::Contravariant => {
                    subst.insert(var, c.max_type().clone());
                }
                Variance::Invariant
                    if matches!(c, Constraint::Eq(eq) if matches!(&eq.ty, Type::Var(v) if &eq.var == v))
                        || matches!(c, Constraint::Subtype(st) if st.lower == st.upper) =>
                {
                    subst.insert(var, c.min_type().clone());
                }
                _ => {}
            };
        }
        subst
    }

    fn any_bounds<F>(&self, tv: &TVar, f: F) -> bool
    where
        F: Fn(&Type) -> bool,
    {
        self.bounds
            .get(tv)
            .map(|tys| tys.iter().any(f))
            .unwrap_or_default()
    }

    // S ∨ T : least upper bound of S and T
    fn least_upper_bound(&self, s: &Type, t: &Type) -> Type {
        if self.verify_subtype(s, t) {
            return t.clone();
        } else if self.verify_subtype(t, s) {
            return s.clone();
        }
        match (s, t) {
            (Type::All(s), Type::All(t)) if s.tyvars == t.tyvars && s.ty == t.ty => {
                let ty = self.least_upper_bound(&s.ty, &t.ty);
                Type::All(TAll {
                    tyvars: s.tyvars.clone(),
                    ty: Box::new(ty),
                })
            }
            (Type::Func(s), Type::Func(t)) if s.params.len() == t.params.len() => {
                let params = s
                    .params
                    .iter()
                    .zip(t.params.iter())
                    .map(|(x, y)| self.greatest_lower_bound(x, y))
                    .collect();
                let ret_ty = self.least_upper_bound(&s.ret_ty, &t.ret_ty);
                Type::Func(TFunc {
                    params,
                    ret_ty: Box::new(ret_ty),
                })
            }
            _ => Type::Top,
        }
    }

    // S ∧ T : greatest lower bound of S and T
    fn greatest_lower_bound(&self, s: &Type, t: &Type) -> Type {
        if self.verify_subtype(s, t) {
            return s.clone();
        } else if self.verify_subtype(t, s) {
            return t.clone();
        }

        match (s, t) {
            (Type::All(s), Type::All(t)) if s.tyvars == t.tyvars && s.ty == t.ty => {
                let ty = self.greatest_lower_bound(&s.ty, &t.ty);
                Type::All(TAll {
                    tyvars: s.tyvars.clone(),
                    ty: Box::new(ty),
                })
            }
            (Type::Func(s), Type::Func(t)) if s.params.len() == t.params.len() => {
                let params = s
                    .params
                    .iter()
                    .zip(t.params.iter())
                    .map(|(x, y)| self.least_upper_bound(x, y))
                    .collect();
                let ret_ty = self.greatest_lower_bound(&s.ret_ty, &t.ret_ty);
                Type::Func(TFunc {
                    params,
                    ret_ty: Box::new(ret_ty),
                })
            }
            _ => Type::Bot,
        }
    }

    pub fn verify_subtype(&self, a: &Type, b: &Type) -> bool {
        println!("{} <: {}?", a, b);
        match (a, b) {
            (Type::Bot, _) | (_, Type::Top) => true,
            (Type::All(a), Type::All(b)) if self.verify_subtype(&a.ty, &b.ty) => true,
            _ if a == b => true,
            _ => self.has_subtype(a, b),
        }
    }

    fn has_subtype(&self, a: &Type, b: &Type) -> bool {
        if a == b || matches!(b, Type::Var(b) if self.any_bounds(b, |x| self.has_subtype(a, x))) {
            return true;
        }

        self.impls
            .get(a)
            .map(|set| set.iter().any(|x| self.has_subtype(x, b)))
            .unwrap_or_default()
    }

    fn constraint_meet(
        &self,
        c1: Constraint,
        c2: Constraint,
    ) -> Result<Constraint, ConstraintGenError> {
        println!("{} ^ {}", c1, c2);
        Ok(match (c1, c2) {
            (Constraint::Eq(c1), Constraint::Eq(c2)) if c1 == c2 => Constraint::Eq(c1),
            (Constraint::Eq(c1), Constraint::Subtype(c2)) if c1.var == c2.var => {
                // Verify that U <: S <: V
                if !self.verify_subtype(&c2.lower, &Type::Var(c1.var.clone())) {
                    return Err(ConstraintGenError(format!(
                        "Cannot unify constraints: {} is not a subtype of {}\n  {}\n  {}",
                        c2.lower, c1.var, c1, c2
                    )));
                }
                if !self.verify_subtype(&Type::Var(c1.var.clone()), &c2.upper) {
                    return Err(ConstraintGenError(format!(
                        "Cannot unify constraints: {} is not a subtype of {}\n  {}\n  {}",
                        c1.var, c2.upper, c1, c2
                    )));
                }
                Constraint::Eq(c1)
            }
            (Constraint::Subtype(c1), Constraint::Eq(c2)) if c1.var == c2.var => {
                // Verify that S <: U <: T
                if !self.verify_subtype(&c1.lower, &Type::Var(c2.var.clone())) {
                    return Err(ConstraintGenError(format!(
                        "Cannot unify constraints: {} is not a subtype of {}\n  {}\n  {}",
                        c1.lower, c2.var, c2, c1
                    )));
                }
                if !self.verify_subtype(&Type::Var(c2.var.clone()), &c1.upper) {
                    return Err(ConstraintGenError(format!(
                        "Cannot unify constraints: {} is not a subtype of {}\n  {}\n  {}",
                        c2.var, c1.upper, c2, c1
                    )));
                }
                Constraint::Eq(c2)
            }
            (Constraint::Subtype(c1), Constraint::Subtype(c2)) => {
                if !self.verify_subtype(&c1.lower, &c1.upper) {
                    return Err(ConstraintGenError(format!(
                        "Cannot unify constraints: {} is not a subtype of {}\n  {}",
                        c1.lower, c1.upper, c1
                    )));
                }

                if !self.verify_subtype(&c2.lower, &c2.upper) {
                    return Err(ConstraintGenError(format!(
                        "Cannot unify constraints: {} is not a subtype of {}\n  {}",
                        c2.lower, c2.upper, c2
                    )));
                }

                let lower = self.least_upper_bound(&c1.lower, &c2.lower);
                let upper = self.greatest_lower_bound(&c1.upper, &c2.upper);
                Constraint::Subtype(SubtypeConstraint {
                    lower,
                    var: c1.var,
                    upper,
                })
            }
            _ => return Err(ConstraintGenError("".to_string())),
        })
    }

    pub fn constraint_set_meet(
        &self,
        cs1: HashMap<TVar, Constraint>,
        mut cs2: HashMap<TVar, Constraint>,
    ) -> Result<HashMap<TVar, Constraint>, ConstraintGenError> {
        let mut m = HashMap::new();
        for (v, c1) in cs1 {
            if let Some(c2) = cs2.remove(&v) {
                m.insert(v, self.constraint_meet(c1, c2)?);
            } else {
                m.insert(v, c1);
            }
        }

        for (v, c2) in cs2 {
            if !m.contains_key(&v) {
                if let Constraint::Subtype(c2) = &c2 {
                    if !self.verify_subtype(&c2.lower, &c2.upper) {
                        return Err(ConstraintGenError(format!(
                            "Cannot unify constraints: {} is not a subtype of {}\n  {}",
                            c2.lower, c2.upper, c2,
                        )));
                    }
                }
                m.insert(v, c2);
            }
        }
        Ok(m)
    }
}
