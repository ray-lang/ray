use std::{collections::{HashMap, HashSet}, fmt::write};

use super::{
    context::TypeContext,
    types::{TVar, Type},
};

pub fn gen_constraints(
    tcx: &TypeContext,
    vars: &HashSet<TVar>,
    unknowns: &HashSet<TVar>,
    a: &Type,
    b: &Type,
) -> Result<HashMap<TVar, Constraint>, ConstraintGenError> {
    println!("gen constraints: {} and {}", a, b);
    match (a, b) {
        (_, Type::Top) | (_, Type::Bot) => return Ok(HashMap::new()),
        _ if a == b => return Ok(HashMap::new()),
        (Type::Var(a), _)
            if unknowns.contains(a) && b.free_vars().iter().all(|v| !unknowns.contains(v)) =>
        {
            let r = b.elim_down(vars, tcx);
            let mut cs = HashMap::new();
            let stc = SubtypeConstraint::new(Type::Bot, a.clone(), r);
            println!("{}", stc);
            cs.insert(a.clone(), stc);
            return Ok(cs);
        }
        (Type::Var(a), _) if tcx.get_bounds(a).is_some() => {
            let mut ret_cs = HashMap::new();
            for bound in tcx.get_bounds(a).unwrap() {
                let cs = gen_constraints(tcx, vars, unknowns, bound, b)?;
                ret_cs = tcx.constraint_set_meet(ret_cs, cs)?;
            }

            return Ok(ret_cs);
        }
        (_, Type::Var(b))
            if unknowns.contains(b) && a.free_vars().iter().all(|v| !unknowns.contains(v)) =>
        {
            let r = a.elim_up(vars, tcx);
            let mut cs = HashMap::new();
            let stc = SubtypeConstraint::new(r, b.clone(), Type::Top);
            println!("{}", stc);
            cs.insert(b.clone(), stc);
            return Ok(cs);
        }
        (Type::Func(a), Type::Func(b)) => {
            return b
                .params
                .iter()
                .zip(a.params.iter())
                .map(|(x, y)| gen_constraints(tcx, vars, unknowns, x, y))
                .chain(std::iter::once(gen_constraints(
                    tcx, vars, unknowns, &a.ret_ty, &b.ret_ty,
                )))
                .try_fold(HashMap::new(), |c, d| {
                    let d = d?;
                    tcx.constraint_set_meet(c, d)
                })
        }
        (Type::All(a), Type::All(b)) => {
            let a_vs_set = a.tyvars.iter().collect::<HashSet<_>>();
            let b_vs_set = b.tyvars.iter().collect::<HashSet<_>>();
            if a_vs_set == b_vs_set
                && a_vs_set
                    .iter()
                    .all(|(v, _)| !vars.contains(v) && !unknowns.contains(v))
            {
                let mut tcx = tcx.clone();
                for (tv, bounds) in a_vs_set.iter() {
                    if let Some(bounds) = bounds {
                        tcx.set_bounds(tv.clone(), bounds.clone());
                    }
                }

                let vs = a_vs_set.iter().map(|(t, _)| t).collect::<HashSet<_>>();
                let vars = vars.iter().collect::<HashSet<_>>();
                let vs_prime = vars
                    .union(&vs)
                    .into_iter()
                    .map(|&a| a.clone())
                    .collect::<HashSet<_>>();
                return gen_constraints(&tcx, &vs_prime, unknowns, &a.ty, &b.ty);
            }
        }
        _ => {} //f'gen_constraints: failed to generate constraints for {{{", ".join(str(v) for v in typevars)}}} ⊢_{{{", ".join(str(x) for x in unknowns)}}} {a} <: {b}'
    };

    Err(ConstraintGenError(format!(
        "gen_constraints: failed to generate constraints for {:?} ⊢_{:?} {} <: {}",
        vars, unknowns, a, b,
    )))

    // if b == TOP or b == BOT or a == b or a is None or b is None {
    //     return {}
    // } else if isinstance(a, TVar) and a in unknowns and len(a.free_vars & unknowns) == 0 {
    //     r = elim_down(typevars, b)
    //     return { a: SubtypeConstraint(BOT, a, r) }
    // } else if isinstance(a, TVar) and a.is_bound {
    //     ret_cs = {}
    //     all_exc = []
    //     for bound in a.bounds:
    //         cs = gen_constraints(tcx, typevars, unknowns, bound, b)
    //         try:
    //             ret_cs = tcx.cs_meet(ret_cs, cs)
    //         except ConstraintGenException as exc:
    //             # preserve the exceptions
    //             all_exc.append(exc)

    //     if len(all_exc) != 0:
    //         # each constraint failed to generate
    //         raise all_exc
    //     return ret_cs
    // } else if isinstance(b, TVar) and b in unknowns and len(a.free_vars & unknowns) == 0 {
    //     r = elim_up(typevars, a)
    //     if not b.is_bound {
    //         return { b: SubtypeConstraint(r, b, TOP) }
    //     }
    //     return reduce(tcx.cs_meet, ({b: SubtypeConstraint(r, b, bound)} for bound in b.bounds))
    // } else if isinstance(a, TAll) and isinstance(b, TAll) {
    //     a_vs, b_vs = set(a.vs), set(b.vs)
    //     ys = a_vs
    //     # NOTE: we only want to know if the vars (not the bounds) are the same
    //     if a_vs == b_vs and len(ys & (typevars | unknowns)) == 0:
    //         vs_prime = typevars | ys
    //         cs = (gen_constraints(tcx, vs_prime, unknowns, x, y) for x, y in zip(b.ts, a.ts))
    //         d = gen_constraints(tcx, vs_prime, unknowns, a.t, b.t)
    //         return tcx.cs_meet(reduce(tcx.cs_meet, cs, {}), d)
    // }

    // // raise ConstraintGenException(f'gen_constraints: failed to generate constraints for {{{", ".join(str(v) for v in typevars)}}} ⊢_{{{", ".join(str(x) for x in unknowns)}}} {a} <: {b}')
    // todo!()
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constraint {
    Eq(EqConstraint),
    Subtype(SubtypeConstraint),
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Eq(c) => write!(f, "{}", c),
            Constraint::Subtype(c) => write!(f, "{}", c),
        }
    }
}

impl Constraint {
    pub fn min_type(&self) -> &Type {
        match self {
            Constraint::Eq(eq) => &eq.ty,
            Constraint::Subtype(st) => &st.lower,
        }
    }

    pub fn max_type(&self) -> &Type {
        match self {
            Constraint::Eq(eq) => &eq.ty,
            Constraint::Subtype(st) => &st.upper,
        }
    }

    pub fn satisfies(&self, ty: &Type, tcx: &TypeContext) -> Option<ConstraintGenError> {
        match self {
            Constraint::Eq(eq) => if &eq.ty != ty {
                Some(ConstraintGenError(
                    format!("{} != {}", eq.ty, ty)
                ))
            } else {
                None
            },
            Constraint::Subtype(st) => {
                if !tcx.verify_subtype(&st.lower, ty) {
                    Some(ConstraintGenError(
                        format!("{} is not a subtype of {}", st.lower, ty)
                    ))
                } else if !tcx.verify_subtype(ty, &st.upper) {
                    Some(ConstraintGenError(
                        format!("{} is not a subtype of {}", ty, st.upper)
                    ))
                } else {
                    None
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EqConstraint {
    pub ty: Type,
    pub var: TVar,
}

impl std::fmt::Display for EqConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} == {}", self.ty, self.var)
    }
}

impl EqConstraint {
    pub fn new(ty: Type, var: TVar) -> Constraint {
        Constraint::Eq(EqConstraint { ty, var })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubtypeConstraint {
    pub lower: Type,
    pub var: TVar,
    pub upper: Type,
}

impl std::fmt::Display for SubtypeConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} <: {} <: {}", self.lower, self.var, self.upper)
    }
}

impl SubtypeConstraint {
    pub fn new(lower: Type, var: TVar, upper: Type) -> Constraint {
        Constraint::Subtype(SubtypeConstraint { lower, var, upper })
    }
}

#[derive(Debug)]
pub struct ConstraintGenError(pub String);

impl std::fmt::Display for ConstraintGenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
