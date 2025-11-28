// Constraint language for the type system.
// This mirrors Section 2 of docs/type-system.md.

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::binding_groups::BindingId;
use crate::info::TypeSystemInfo;
use crate::types::{Subst, Substitutable, Ty, TyVar};

// Class predicates: trait-like constraints C[Recv, A1, ..., An].
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ClassPredicate {
    // For now, we use a simple path-like name; this can be refined later.
    pub name: String,
    pub args: Vec<Ty>,
}

impl ClassPredicate {
    pub fn new(name: impl Into<String>, args: Vec<Ty>) -> Self {
        ClassPredicate {
            name: name.into(),
            args,
        }
    }

    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        for arg in &self.args {
            arg.free_ty_vars(out);
        }
    }
}

// HasField[RecordTy, FieldName, FieldTy].
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HasFieldPredicate {
    pub record_ty: Ty,
    pub field_name: String,
    pub field_ty: Ty,
}

impl HasFieldPredicate {
    pub fn new(record_ty: Ty, field_name: impl Into<String>, field_ty: Ty) -> Self {
        HasFieldPredicate {
            record_ty,
            field_name: field_name.into(),
            field_ty,
        }
    }

    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        self.record_ty.free_ty_vars(out);
        self.field_ty.free_ty_vars(out);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RecvKind {
    Value,
    Ref,
}

// Recv[RecvTy, ExprTy].
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RecvPredicate {
    pub kind: RecvKind,
    pub recv_ty: Ty,
    pub expr_ty: Ty,
}

impl RecvPredicate {
    pub fn new(kind: RecvKind, recv_ty: Ty, expr_ty: Ty) -> Self {
        RecvPredicate {
            kind,
            recv_ty,
            expr_ty,
        }
    }

    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        self.recv_ty.free_ty_vars(out);
        self.expr_ty.free_ty_vars(out);
    }
}

// Equality constraints t1 == t2.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EqConstraint {
    pub lhs: Ty,
    pub rhs: Ty,
}

impl EqConstraint {
    pub fn new(lhs: Ty, rhs: Ty) -> Self {
        EqConstraint { lhs, rhs }
    }
}

// Equality constraints t1 == t2.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InstantiateConstraint {
    pub binding: BindingId,
    pub ty: Ty,
}

impl InstantiateConstraint {
    pub fn new(binding: BindingId, ty: Ty) -> Self {
        InstantiateConstraint { binding, ty }
    }
}

/// Logical predicates used as qualifiers on schemes and as the non-equality
/// part of constraints.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Predicate {
    Class(ClassPredicate),
    HasField(HasFieldPredicate),
    Recv(RecvPredicate),
}

impl Predicate {
    pub fn class(name: impl Into<String>, args: Vec<Ty>) -> Predicate {
        Predicate::Class(ClassPredicate {
            name: name.into(),
            args,
        })
    }

    pub fn has_field(record_ty: Ty, field_name: impl Into<String>, field_ty: Ty) -> Predicate {
        Predicate::HasField(HasFieldPredicate {
            record_ty,
            field_name: field_name.into(),
            field_ty: field_ty,
        })
    }

    pub fn recv(kind: RecvKind, recv_ty: Ty, expr_ty: Ty) -> Predicate {
        Predicate::Recv(RecvPredicate {
            kind,
            recv_ty,
            expr_ty,
        })
    }

    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        match self {
            Predicate::Class(p) => p.free_ty_vars(out),
            Predicate::HasField(p) => p.free_ty_vars(out),
            Predicate::Recv(p) => p.free_ty_vars(out),
        }
    }
}

// Unified constraint kind used in the solver pipeline.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConstraintKind {
    Eq(EqConstraint),
    Instantiate(InstantiateConstraint),
    Class(ClassPredicate),
    HasField(HasFieldPredicate),
    Recv(RecvPredicate),
}

/// A constraint annotated with type-system information.
///
/// The `info` field is used to thread source locations and other contextual
/// details from constraint generation through the solvers into diagnostics.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constraint {
    pub kind: ConstraintKind,
    pub info: TypeSystemInfo,
}

impl Constraint {
    pub fn eq(lhs: Ty, rhs: Ty, info: TypeSystemInfo) -> Self {
        Constraint {
            kind: ConstraintKind::Eq(EqConstraint::new(lhs, rhs)),
            info,
        }
    }

    pub fn class(name: impl Into<String>, args: Vec<Ty>, info: TypeSystemInfo) -> Self {
        Constraint {
            kind: ConstraintKind::Class(ClassPredicate::new(name, args)),
            info,
        }
    }

    pub fn has_field(
        record_ty: Ty,
        field_name: impl Into<String>,
        field_ty: Ty,
        info: TypeSystemInfo,
    ) -> Self {
        Constraint {
            kind: ConstraintKind::HasField(HasFieldPredicate::new(record_ty, field_name, field_ty)),
            info,
        }
    }

    pub fn recv(kind: RecvKind, recv_ty: Ty, expr_ty: Ty, info: TypeSystemInfo) -> Self {
        Constraint {
            kind: ConstraintKind::Recv(RecvPredicate::new(kind, recv_ty, expr_ty)),
            info,
        }
    }

    pub fn inst(binding: BindingId, ty: Ty, info: TypeSystemInfo) -> Self {
        Constraint {
            kind: ConstraintKind::Instantiate(InstantiateConstraint { binding, ty }),
            info,
        }
    }

    /// Construct a constraint from an existing predicate payload.
    pub fn from_predicate(predicate: Predicate, info: TypeSystemInfo) -> Self {
        let kind = match predicate {
            Predicate::Class(c) => ConstraintKind::Class(c),
            Predicate::HasField(h) => ConstraintKind::HasField(h),
            Predicate::Recv(r) => ConstraintKind::Recv(r),
        };
        Constraint { kind, info }
    }

    /// If this constraint represents a logical predicate (as opposed to an equality),
    /// return it as a standalone `Predicate`.
    pub fn to_predicate(&self) -> Option<Predicate> {
        match &self.kind {
            ConstraintKind::Class(c) => Some(Predicate::Class(c.clone())),
            ConstraintKind::HasField(h) => Some(Predicate::HasField(h.clone())),
            ConstraintKind::Recv(r) => Some(Predicate::Recv(r.clone())),
            ConstraintKind::Eq(_) | ConstraintKind::Instantiate(_) => None,
        }
    }

    /// Collect all the free variables from the constraint
    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        match &self.kind {
            ConstraintKind::Class(cl) => {
                for arg in cl.args.iter() {
                    arg.free_ty_vars(out);
                }
            }
            ConstraintKind::HasField(hp) => {
                hp.record_ty.free_ty_vars(out);
                hp.field_ty.free_ty_vars(out);
            }
            ConstraintKind::Recv(rp) => {
                rp.recv_ty.free_ty_vars(out);
                rp.expr_ty.free_ty_vars(out);
            }
            ConstraintKind::Eq(eq) => {
                eq.lhs.free_ty_vars(out);
                eq.rhs.free_ty_vars(out);
            }
            ConstraintKind::Instantiate(inst) => {
                inst.ty.free_ty_vars(out);
            }
        }
    }
}

impl Substitutable for ClassPredicate {
    fn apply_subst(&mut self, subst: &Subst) {
        for arg in &mut self.args {
            arg.apply_subst(subst);
        }
    }
}

impl Substitutable for HasFieldPredicate {
    fn apply_subst(&mut self, subst: &Subst) {
        self.record_ty.apply_subst(subst);
        self.field_ty.apply_subst(subst);
    }
}

impl Substitutable for RecvPredicate {
    fn apply_subst(&mut self, subst: &Subst) {
        self.recv_ty.apply_subst(subst);
        self.expr_ty.apply_subst(subst);
    }
}

impl Substitutable for EqConstraint {
    fn apply_subst(&mut self, subst: &Subst) {
        self.lhs.apply_subst(subst);
        self.rhs.apply_subst(subst);
    }
}

impl Substitutable for InstantiateConstraint {
    fn apply_subst(&mut self, subst: &Subst) {
        self.ty.apply_subst(subst);
    }
}

impl Substitutable for Predicate {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Predicate::Class(c) => c.apply_subst(subst),
            Predicate::HasField(c) => c.apply_subst(subst),
            Predicate::Recv(c) => c.apply_subst(subst),
        }
    }
}

impl Substitutable for ConstraintKind {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            ConstraintKind::Eq(c) => c.apply_subst(subst),
            ConstraintKind::Instantiate(c) => c.apply_subst(subst),
            ConstraintKind::Class(c) => c.apply_subst(subst),
            ConstraintKind::HasField(c) => c.apply_subst(subst),
            ConstraintKind::Recv(c) => c.apply_subst(subst),
        }
    }
}

impl Substitutable for Constraint {
    fn apply_subst(&mut self, subst: &Subst) {
        self.kind.apply_subst(subst);
        self.info.apply_subst(subst);
    }
}

impl std::fmt::Display for ConstraintKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintKind::Eq(eq) => write!(f, "{}", eq),
            ConstraintKind::Instantiate(inst) => write!(f, "{}", inst),
            ConstraintKind::Class(c) => write!(f, "{}", c),
            ConstraintKind::HasField(h) => write!(f, "{}", h),
            ConstraintKind::Recv(r) => write!(f, "{}", r),
        }
    }
}

impl std::fmt::Display for ClassPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let args = self
            .args
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}[{}]", self.name, args)
    }
}

impl std::fmt::Display for HasFieldPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "HasField[{}, {}, {}]",
            self.record_ty, self.field_name, self.field_ty
        )
    }
}

impl std::fmt::Display for RecvPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Recv[{:?}, {}, {}]",
            self.kind, self.recv_ty, self.expr_ty
        )
    }
}

impl std::fmt::Display for EqConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} == {}", self.lhs, self.rhs)
    }
}

impl std::fmt::Display for InstantiateConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Instantiate({}, {})", self.binding, self.ty)
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl std::fmt::Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::Class(c) => write!(f, "{}", c),
            Predicate::HasField(h) => write!(f, "{}", h),
            Predicate::Recv(r) => write!(f, "{}", r),
        }
    }
}
