use std::fmt::Display;

use crate::constraints::Predicate;
use crate::types::{Subst, Substitutable, Ty, TyScheme, TyVar};
use ray_shared::span::Source;
use serde::{Deserialize, Serialize};

/// Additional contextual information for type errors and diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Info {
    EqualityTypePair(Ty, Ty),
    MissingPredicate(Predicate),
    AmbiguousPredicate(Predicate),
    UnsolvedPredicate(Predicate, Box<TypeSystemInfo>),
    PredicateArisingFrom(Predicate),
    ParentPredicate(Predicate),
    EscapedSkolems(Vec<TyVar>),
    NeverDirective(Predicate, Box<TypeSystemInfo>),
    CloseDirective(String, Box<TypeSystemInfo>),
    DisjointDirective(String, Box<TypeSystemInfo>, String, Box<TypeSystemInfo>),
    InstantiatedTypeScheme(TyScheme),
    SkolemizedTypeScheme(Vec<Ty>, TyScheme),
    Detail(String),
}

impl Substitutable for Info {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Info::EqualityTypePair(t1, t2) => {
                t1.apply_subst(subst);
                t2.apply_subst(subst);
            }
            Info::MissingPredicate(pred)
            | Info::AmbiguousPredicate(pred)
            | Info::PredicateArisingFrom(pred)
            | Info::ParentPredicate(pred) => pred.apply_subst(subst),
            Info::UnsolvedPredicate(pred, info) | Info::NeverDirective(pred, info) => {
                pred.apply_subst(subst);
                info.apply_subst(subst);
            }
            Info::CloseDirective(_, info) => {
                info.apply_subst(subst);
            }
            Info::DisjointDirective(_, lhs, _, rhs) => {
                lhs.apply_subst(subst);
                rhs.apply_subst(subst);
            }
            Info::InstantiatedTypeScheme(scheme) => {
                scheme.apply_subst(subst);
            }
            Info::SkolemizedTypeScheme(tys, scheme) => {
                for ty in tys {
                    ty.apply_subst(subst);
                }
                scheme.apply_subst(subst);
            }
            Info::EscapedSkolems(_) | Info::Detail(_) => {}
        }
    }
}

impl Display for Info {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Info::EqualityTypePair(a, b) => write!(f, "EqualityTypePair({}, {})", a, b),
            Info::MissingPredicate(p) => write!(f, "MissingPredicate({})", p),
            Info::AmbiguousPredicate(p) => write!(f, "AmbiguousPredicate({})", p),
            Info::UnsolvedPredicate(p, _) => write!(f, "UnsolvedPredicate({})", p),
            Info::PredicateArisingFrom(p) => write!(f, "PredicateArisingFrom({})", p),
            Info::ParentPredicate(p) => write!(f, "ParentPredicate({})", p),
            Info::EscapedSkolems(vars) => write!(f, "EscapedSkolems({:?})", vars),
            Info::NeverDirective(p, _) => write!(f, "NeverDirective({})", p),
            Info::CloseDirective(name, _) => write!(f, "CloseDirective({})", name),
            Info::DisjointDirective(lhs, _, rhs, _) => {
                write!(f, "DisjointDirective({}, {})", lhs, rhs)
            }
            Info::InstantiatedTypeScheme(s) => write!(f, "InstantiatedTypeScheme({})", s),
            Info::SkolemizedTypeScheme(vars, s) => {
                write!(f, "SkolemizedTypeScheme({:?}, {})", vars, s)
            }
            Info::Detail(msg) => write!(f, "Detail({})", msg),
        }
    }
}

/// Aggregated type-system information for an error.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeSystemInfo {
    pub info: Vec<Info>,
    pub source: Vec<Source>,
}

impl TypeSystemInfo {
    pub fn new() -> Self {
        TypeSystemInfo::default()
    }

    pub fn with_src(&mut self, src: Source) {
        self.source.push(src);
    }

    pub fn extend(&mut self, other: TypeSystemInfo) {
        self.info.extend(other.info);
        self.source.extend(other.source);
    }

    pub fn simplify(&mut self) {
        self.info.retain(|info| match info {
            Info::EqualityTypePair(t1, t2) => t1 != t2,
            _ => true,
        });
    }

    /// Record an equality-type-pair detail.
    pub fn equality_type_pair(&mut self, lhs: &Ty, rhs: &Ty) {
        self.info
            .push(Info::EqualityTypePair(lhs.clone(), rhs.clone()));
    }

    /// Record a missing predicate detail.
    pub fn missing_predicate(&mut self, predicate: &Predicate) {
        self.info.push(Info::MissingPredicate(predicate.clone()));
    }

    /// Record an ambiguous predicate detail.
    pub fn ambiguous_predicate(&mut self, predicate: &Predicate) {
        self.info.push(Info::AmbiguousPredicate(predicate.clone()));
    }

    /// Record an unsolved predicate detail, preserving the contributing info.
    pub fn unsolved_predicate(&mut self, predicate: &Predicate, info: &TypeSystemInfo) {
        self.info.push(Info::UnsolvedPredicate(
            predicate.clone(),
            Box::new(info.clone()),
        ));
    }

    /// Record where a predicate obligation originated.
    pub fn predicate_arising_from(&mut self, predicate: &Predicate) {
        self.info
            .push(Info::PredicateArisingFrom(predicate.clone()));
    }

    /// Record the parent predicate (e.g. enclosing context) for diagnostics.
    pub fn parent_predicate(&mut self, predicate: &Predicate) {
        self.info.push(Info::ParentPredicate(predicate.clone()));
    }

    /// Record skolems that attempted to escape their scope.
    pub fn escaped_skolems(&mut self, skolems: &[TyVar]) {
        self.info.push(Info::EscapedSkolems(skolems.to_vec()));
    }

    /// Record that a predicate should never hold (a `never` directive).
    pub fn never_directive(&mut self, predicate: &Predicate, info: &TypeSystemInfo) {
        self.info.push(Info::NeverDirective(
            predicate.clone(),
            Box::new(info.clone()),
        ));
    }

    /// Record a `close` directive along with supporting info.
    pub fn close_directive(&mut self, directive: &String, info: &TypeSystemInfo) {
        self.info.push(Info::CloseDirective(
            directive.clone(),
            Box::new(info.clone()),
        ));
    }

    /// Record a `disjoint` directive between two trait/type combinations.
    pub fn disjoint_directive(
        &mut self,
        lhs: &String,
        lhs_info: &TypeSystemInfo,
        rhs: &String,
        rhs_info: &TypeSystemInfo,
    ) {
        self.info.push(Info::DisjointDirective(
            lhs.clone(),
            Box::new(lhs_info.clone()),
            rhs.clone(),
            Box::new(rhs_info.clone()),
        ));
    }

    /// Record that a type scheme was instantiated during solving.
    pub fn instantiated_type_scheme(&mut self, scheme: &TyScheme) {
        self.info.push(Info::InstantiatedTypeScheme(scheme.clone()));
    }

    /// Record that a scheme was skolemized, along with the resulting skolems.
    pub fn skolemized_type_scheme(&mut self, vars: &[TyVar], scheme: &TyScheme) {
        self.info.push(Info::SkolemizedTypeScheme(
            vars.iter().cloned().map(|v| Ty::Var(v)).collect(),
            scheme.clone(),
        ));
    }

    /// Record a free-form detail string.
    pub fn detail(&mut self, msg: impl Into<String>) {
        self.info.push(Info::Detail(msg.into()));
    }
}

impl Substitutable for TypeSystemInfo {
    fn apply_subst(&mut self, subst: &Subst) {
        for info in &mut self.info {
            info.apply_subst(subst);
        }
    }
}

impl Display for TypeSystemInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.info.is_empty() {
            return write!(
                f,
                "TypeSystemInfo(source=[{}])",
                self.source
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }

        writeln!(f, "TypeSystemInfo(")?;
        writeln!(
            f,
            "  source=[{}]",
            self.source
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        writeln!(f, "  info=[")?;
        for info in &self.info {
            writeln!(f, "    {}", info)?;
        }
        write!(f, "  ]\n)")
    }
}
