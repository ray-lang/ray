// Constraint language for the type system.
// This mirrors Section 2 of docs/type-system.md.

use std::collections::HashSet;

use ray_shared::ty::{Ty, TyVar};
use serde::{Deserialize, Serialize};

use crate::{
    binding_groups::BindingId,
    info::TypeSystemInfo,
    types::{Subst, Substitutable},
};

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

    pub fn is_ground(&self) -> bool {
        self.args.iter().all(|t| t.free_vars().is_empty())
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstantiateConstraint {
    pub binding: BindingId,
    pub ty: Ty,
    /// Optional pre-substitution to apply to the binding's scheme at this use
    /// site before instantiation.
    ///
    /// This is used for associated member references like `T::member` where
    /// the left-hand side type `T[...]` determines how impl-scoped schema
    /// variables in the member scheme should be rewritten.
    pub receiver_subst: Option<Subst>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallKind {
    /// `recv.method(args...)`
    Instance,
    /// `T::method(args...)` or `T[...]::method(args...)`
    Scoped {
        binding: BindingId,
        receiver_subst: Option<Subst>,
    },
}

/// Deferred resolution of a member call.
///
/// This is emitted during constraint generation for member-call syntax when
/// the receiver/LHS type is not yet known (it is often still a meta variable
/// at this phase). The solver is responsible for resolving this into the
/// existing constraint forms (Instantiate/Eq/Recv) once the subject type is
/// headed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolveCallConstraint {
    pub kind: CallKind,
    /// Receiver type (for instance calls) or LHS type (for scoped calls).
    pub subject_ty: Ty,
    /// Expected function type at the call site, including the receiver.
    pub expected_fn_ty: Ty,
    /// Name of the method for the call
    pub method_name: String,
}

impl ResolveCallConstraint {
    pub fn new_instance(
        subject_ty: Ty,
        method_name: impl Into<String>,
        expected_fn_ty: Ty,
    ) -> Self {
        let method_name = method_name.into();
        ResolveCallConstraint {
            kind: CallKind::Instance,
            subject_ty,
            expected_fn_ty,
            method_name,
        }
    }

    pub fn new_scoped(
        subject_ty: Ty,
        binding: BindingId,
        expected_fn_ty: Ty,
        method_name: impl Into<String>,
        receiver_subst: Option<Subst>,
    ) -> Self {
        let method_name = method_name.into();
        ResolveCallConstraint {
            kind: CallKind::Scoped {
                binding,
                receiver_subst,
            },
            subject_ty,
            expected_fn_ty,
            method_name,
        }
    }

    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        self.subject_ty.free_ty_vars(out);
        self.expected_fn_ty.free_ty_vars(out);
        if let CallKind::Scoped {
            receiver_subst: Some(receiver_subst),
            ..
        } = &self.kind
        {
            for ty in receiver_subst.values() {
                ty.free_ty_vars(out);
            }
        }
    }
}

impl InstantiateConstraint {
    pub fn new(binding: BindingId, ty: Ty) -> Self {
        InstantiateConstraint {
            binding,
            ty,
            receiver_subst: None,
        }
    }

    pub fn new_with_receiver_subst(binding: BindingId, ty: Ty, receiver_subst: Subst) -> Self {
        InstantiateConstraint {
            binding,
            ty,
            receiver_subst: Some(receiver_subst),
        }
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstraintKind {
    Eq(EqConstraint),
    Instantiate(InstantiateConstraint),
    ResolveCall(ResolveCallConstraint),
    Class(ClassPredicate),
    HasField(HasFieldPredicate),
    Recv(RecvPredicate),
}

/// A constraint annotated with type-system information.
///
/// The `info` field is used to thread source locations and other contextual
/// details from constraint generation through the solvers into diagnostics.
#[derive(Clone, Debug, PartialEq, Eq)]
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
            kind: ConstraintKind::Instantiate(InstantiateConstraint::new(binding, ty)),
            info,
        }
    }

    pub fn inst_with_receiver_subst(
        binding: BindingId,
        ty: Ty,
        receiver_subst: Subst,
        info: TypeSystemInfo,
    ) -> Self {
        Constraint {
            kind: ConstraintKind::Instantiate(InstantiateConstraint::new_with_receiver_subst(
                binding,
                ty,
                receiver_subst,
            )),
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
            ConstraintKind::Eq(_)
            | ConstraintKind::Instantiate(_)
            | ConstraintKind::ResolveCall(_) => None,
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
                if let Some(receiver_subst) = &inst.receiver_subst {
                    for ty in receiver_subst.values() {
                        ty.free_ty_vars(out);
                    }
                }
            }
            ConstraintKind::ResolveCall(call) => {
                call.free_ty_vars(out);
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
        if let Some(receiver_subst) = &mut self.receiver_subst {
            for ty in receiver_subst.values_mut() {
                ty.apply_subst(subst);
            }
        }
    }
}

impl Substitutable for ResolveCallConstraint {
    fn apply_subst(&mut self, subst: &Subst) {
        self.subject_ty.apply_subst(subst);
        self.expected_fn_ty.apply_subst(subst);
        if let CallKind::Scoped {
            receiver_subst: Some(receiver_subst),
            ..
        } = &mut self.kind
        {
            for ty in receiver_subst.values_mut() {
                ty.apply_subst(subst);
            }
        }
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
            ConstraintKind::ResolveCall(c) => c.apply_subst(subst),
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
            ConstraintKind::ResolveCall(call) => write!(f, "{}", call),
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
        if let Some(receiver_subst) = &self.receiver_subst {
            write!(
                f,
                "Instantiate({}, {}, receiver_subst = {:#})",
                self.binding, self.ty, receiver_subst
            )
        } else {
            write!(f, "Instantiate({}, {})", self.binding, self.ty)
        }
    }
}

impl std::fmt::Display for ResolveCallConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let method_name = &self.method_name;
        let kind_str = match &self.kind {
            CallKind::Instance => {
                format!("Instance")
            }
            CallKind::Scoped { binding, .. } => format!("Scoped {{ binding: {:?} }}", binding),
        };
        write!(
            f,
            "ResolveCall({}, {}, {}: expected_fn_ty = {})",
            kind_str, self.subject_ty, method_name, self.expected_fn_ty
        )
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
