// Constraint language for the type system.
// This mirrors Section 2 of docs/type-system.md.

use std::collections::HashSet;

use ray_shared::{
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::ItemPath,
    resolution::DefTarget,
    ty::{Ty, TyVar},
};
use serde::{Deserialize, Serialize};

use crate::{
    info::TypeSystemInfo,
    types::{Subst, Substitutable},
};

// Class predicates: trait-like constraints C[Recv, A1, ..., An].
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ClassPredicate {
    pub path: ItemPath,
    pub args: Vec<Ty>,
}

impl ClassPredicate {
    pub fn new(path: impl Into<ItemPath>, args: Vec<Ty>) -> Self {
        ClassPredicate {
            path: path.into(),
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

// Instantiate constraint: instantiate a definition's or binding's scheme.

/// Target of an instantiation constraint - either a top-level definition
/// (workspace or library) or a local binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstantiateTarget {
    /// A top-level definition (workspace or library).
    Def(DefTarget),
    /// A local binding (parameters, let-bindings, etc.)
    Local(LocalBindingId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstantiateConstraint {
    pub target: InstantiateTarget,
    pub ty: Ty,
    /// Optional pre-substitution to apply to the def's scheme at this use
    /// site before instantiation.
    ///
    /// This is used for associated member references like `T::member` where
    /// the left-hand side type `T[...]` determines how impl-scoped schema
    /// variables in the member scheme should be rewritten.
    pub receiver_subst: Option<Subst>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberAccessKind {
    /// `recv.member(args...)` - instance member call
    InstanceCall,
    /// `T::member(args...)` or `T[...]::member(args...)` - scoped member call
    ///
    /// Unlike InstanceCall, the member is resolved by name on the explicit subject
    /// type rather than an inferred receiver type. The solver looks up the
    /// member the same way as InstanceCall.
    ScopedCall { receiver_subst: Option<Subst> },
    /// `T::member` - scoped member access (non-call, e.g., constant or fn as value)
    ///
    /// Same resolution as ScopedCall but not a call expression - the member's
    /// type scheme is instantiated and unified with the expected type.
    ScopedAccess { receiver_subst: Option<Subst> },
}

/// Deferred resolution of a member access.
///
/// This is emitted during constraint generation for member access syntax when
/// the receiver/LHS type is not yet known (it is often still a meta variable
/// at this phase). The solver is responsible for resolving this into the
/// existing constraint forms (Instantiate/Eq/Recv) once the subject type is
/// headed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolveMemberConstraint {
    pub kind: MemberAccessKind,
    /// Receiver type (for instance calls) or LHS type (for scoped access).
    pub subject_ty: Ty,
    /// Expected type - function type for calls, member's type for non-call access.
    pub expected_ty: Ty,
    /// Name of the member being accessed.
    pub member_name: String,
    /// The NodeId of the expression, used to key the method resolution side-table.
    pub site: NodeId,
}

impl ResolveMemberConstraint {
    pub fn new_instance(
        subject_ty: Ty,
        member_name: impl Into<String>,
        expected_ty: Ty,
        site: NodeId,
    ) -> Self {
        let member_name = member_name.into();
        ResolveMemberConstraint {
            kind: MemberAccessKind::InstanceCall,
            subject_ty,
            expected_ty,
            member_name,
            site,
        }
    }

    pub fn new_scoped_call(
        subject_ty: Ty,
        expected_ty: Ty,
        member_name: impl Into<String>,
        receiver_subst: Option<Subst>,
        site: NodeId,
    ) -> Self {
        let member_name = member_name.into();
        ResolveMemberConstraint {
            kind: MemberAccessKind::ScopedCall { receiver_subst },
            subject_ty,
            expected_ty,
            member_name,
            site,
        }
    }

    pub fn new_scoped_access(
        subject_ty: Ty,
        expected_ty: Ty,
        member_name: impl Into<String>,
        receiver_subst: Option<Subst>,
        site: NodeId,
    ) -> Self {
        let member_name = member_name.into();
        ResolveMemberConstraint {
            kind: MemberAccessKind::ScopedAccess { receiver_subst },
            subject_ty,
            expected_ty,
            member_name,
            site,
        }
    }

    pub fn free_ty_vars(&self, out: &mut HashSet<TyVar>) {
        self.subject_ty.free_ty_vars(out);
        self.expected_ty.free_ty_vars(out);
        match &self.kind {
            MemberAccessKind::ScopedCall {
                receiver_subst: Some(subst),
            }
            | MemberAccessKind::ScopedAccess {
                receiver_subst: Some(subst),
            } => {
                for ty in subst.values() {
                    ty.free_ty_vars(out);
                }
            }
            _ => {}
        }
    }
}

impl InstantiateConstraint {
    pub fn new_def(target: DefTarget, ty: Ty) -> Self {
        InstantiateConstraint {
            target: InstantiateTarget::Def(target),
            ty,
            receiver_subst: None,
        }
    }

    pub fn new_local(local_id: LocalBindingId, ty: Ty) -> Self {
        InstantiateConstraint {
            target: InstantiateTarget::Local(local_id),
            ty,
            receiver_subst: None,
        }
    }

    pub fn new_def_with_receiver_subst(target: DefTarget, ty: Ty, receiver_subst: Subst) -> Self {
        InstantiateConstraint {
            target: InstantiateTarget::Def(target),
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
    /// Convert a type to a predicate (for where clauses).
    pub fn from_ty(ty: &Ty) -> Option<Predicate> {
        match ty {
            Ty::Proj(path, args) => Some(Predicate::class(path.clone(), args.clone())),
            Ty::Const(path) => Some(Predicate::class(path.clone(), vec![])),
            _ => None,
        }
    }

    pub fn class(path: impl Into<ItemPath>, args: Vec<Ty>) -> Predicate {
        Predicate::Class(ClassPredicate {
            path: path.into(),
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
    ResolveMember(ResolveMemberConstraint),
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

    pub fn class(path: impl Into<ItemPath>, args: Vec<Ty>, info: TypeSystemInfo) -> Self {
        Constraint {
            kind: ConstraintKind::Class(ClassPredicate::new(path, args)),
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

    pub fn inst(target: DefTarget, ty: Ty, info: TypeSystemInfo) -> Self {
        Constraint {
            kind: ConstraintKind::Instantiate(InstantiateConstraint::new_def(target, ty)),
            info,
        }
    }

    pub fn inst_local(local_id: LocalBindingId, ty: Ty, info: TypeSystemInfo) -> Self {
        Constraint {
            kind: ConstraintKind::Instantiate(InstantiateConstraint::new_local(local_id, ty)),
            info,
        }
    }

    pub fn inst_with_receiver_subst(
        target: DefTarget,
        ty: Ty,
        receiver_subst: Subst,
        info: TypeSystemInfo,
    ) -> Self {
        Constraint {
            kind: ConstraintKind::Instantiate(InstantiateConstraint::new_def_with_receiver_subst(
                target,
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
            | ConstraintKind::ResolveMember(_) => None,
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
            ConstraintKind::ResolveMember(member) => {
                member.free_ty_vars(out);
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

impl Substitutable for ResolveMemberConstraint {
    fn apply_subst(&mut self, subst: &Subst) {
        self.subject_ty.apply_subst(subst);
        self.expected_ty.apply_subst(subst);
        match &mut self.kind {
            MemberAccessKind::ScopedCall {
                receiver_subst: Some(rs),
            }
            | MemberAccessKind::ScopedAccess {
                receiver_subst: Some(rs),
            } => {
                for ty in rs.values_mut() {
                    ty.apply_subst(subst);
                }
            }
            _ => {}
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
            ConstraintKind::ResolveMember(c) => c.apply_subst(subst),
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
            ConstraintKind::ResolveMember(member) => write!(f, "{}", member),
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
        write!(f, "{}[{}]", self.path, args)
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
                "Instantiate({:?}, {}, receiver_subst = {:#})",
                self.target, self.ty, receiver_subst
            )
        } else {
            write!(f, "Instantiate({:?}, {})", self.target, self.ty)
        }
    }
}

impl std::fmt::Display for ResolveMemberConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let member_name = &self.member_name;
        let kind_str = match &self.kind {
            MemberAccessKind::InstanceCall => "InstanceCall".to_string(),
            MemberAccessKind::ScopedCall { receiver_subst } => {
                if receiver_subst.is_some() {
                    "ScopedCall { with_receiver_subst }".to_string()
                } else {
                    "ScopedCall".to_string()
                }
            }
            MemberAccessKind::ScopedAccess { receiver_subst } => {
                if receiver_subst.is_some() {
                    "ScopedAccess { with_receiver_subst }".to_string()
                } else {
                    "ScopedAccess".to_string()
                }
            }
        };
        write!(
            f,
            "ResolveMember({}, {}, {}: expected_ty = {})",
            kind_str, self.subject_ty, member_name, self.expected_ty
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
