use std::fmt::Display;

use serde::{Deserialize, Serialize};
use top::{
    util::Join, InfoDetail, PolyTypeConstraintInfo, Predicate, Predicates, Scheme,
    TypeConstraintInfo,
};

use crate::span::Source;

use super::ty::{Ty, TyVar};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Info {
    EqualityTypePair(Ty, Ty),
    AmbiguousPredicate(Predicate<Ty, TyVar>),
    UnsolvedPredicate(Predicate<Ty, TyVar>, Box<TypeSystemInfo>),
    PredicateArisingFrom(Predicate<Ty, TyVar>),
    ParentPredicate(Predicate<Ty, TyVar>),
    EscapedSkolems(Vec<TyVar>),
    NeverDirective(Predicate<Ty, TyVar>, Box<TypeSystemInfo>),
    CloseDirective(String, Box<TypeSystemInfo>),
    DisjointDirective(String, Box<TypeSystemInfo>, String, Box<TypeSystemInfo>),
    InstantiatedTypeScheme(Scheme<Predicates<Ty, TyVar>, Ty, TyVar>),
    SkolemizedTypeScheme(Vec<Ty>, Scheme<Predicates<Ty, TyVar>, Ty, TyVar>),
    Detail(String),
}

impl Display for Info {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Info::EqualityTypePair(a, b) => write!(f, "EqualityTypePair({}, {})", a, b),
            Info::AmbiguousPredicate(p) => write!(f, "AmbiguousPredicate({})", p),
            Info::UnsolvedPredicate(p, _) => write!(f, "UnsolvedPredicate({})", p),
            Info::PredicateArisingFrom(p) => write!(f, "PredicateArisingFrom({})", p),
            Info::ParentPredicate(p) => write!(f, "ParentPredicate({})", p),
            Info::EscapedSkolems(vars) => write!(f, "EscapedSkolems({:?})", vars),
            Info::NeverDirective(p, _) => write!(f, "NeverDirective({})", p),
            Info::CloseDirective(name, _) => write!(f, "CloseDirective({})", name),
            Info::DisjointDirective(name1, _, name2, _) => {
                write!(f, "DisjointDirective({}, {})", name1, name2)
            }
            Info::InstantiatedTypeScheme(s) => {
                write!(f, "InstantiatedTypeScheme({})", s)
            }
            Info::SkolemizedTypeScheme(vars, s) => {
                write!(f, "SkolemizedTypeScheme({:?}, {})", vars, s)
            }
            Info::Detail(s) => write!(f, "Detail({})", s),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeSystemInfo {
    pub info: Vec<Info>,
    pub source: Vec<Source>,
}

impl Display for TypeSystemInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.info.is_empty() {
            return write!(
                f,
                "TypeSystemInfo(source=[{}])",
                self.source.iter().join(", ")
            );
        }

        write!(f, "TypeSystemInfo(\n")?;
        write!(f, "  source=[{}]\n", self.source.iter().join(", "))?;
        write!(f, "  info=[\n")?;
        for info in self.info.iter() {
            write!(f, "  {}\n", info)?;
        }
        write!(f, "])")
    }
}

impl InfoDetail for TypeSystemInfo {
    fn add_detail(&mut self, detail: &str) {
        self.info.push(Info::Detail(detail.to_string()));
    }
}

impl TypeConstraintInfo<TypeSystemInfo, Ty, TyVar> for TypeSystemInfo {
    fn equality_type_pair(&mut self, lhs: &Ty, rhs: &Ty) {
        self.info
            .push(Info::EqualityTypePair(lhs.clone(), rhs.clone()));
    }

    fn ambiguous_predicate(&mut self, predicate: &Predicate<Ty, TyVar>) {
        self.info.push(Info::AmbiguousPredicate(predicate.clone()));
    }

    fn unsolved_predicate(&mut self, predicate: &Predicate<Ty, TyVar>, info: &TypeSystemInfo) {
        self.info.push(Info::UnsolvedPredicate(
            predicate.clone(),
            Box::new(info.clone()),
        ));
    }

    fn predicate_arising_from(&mut self, predicate: &Predicate<Ty, TyVar>) {
        self.info
            .push(Info::PredicateArisingFrom(predicate.clone()));
    }

    fn parent_predicate(&mut self, predicate: &Predicate<Ty, TyVar>) {
        self.info.push(Info::ParentPredicate(predicate.clone()));
    }

    fn escaped_skolems(&mut self, skolems: &[TyVar]) {
        self.info.push(Info::EscapedSkolems(skolems.to_vec()));
    }

    fn never_directive(&mut self, predicate: &Predicate<Ty, TyVar>, info: &TypeSystemInfo) {
        self.info.push(Info::NeverDirective(
            predicate.clone(),
            Box::new(info.clone()),
        ));
    }

    fn close_directive(&mut self, directive: &String, info: &TypeSystemInfo) {
        self.info.push(Info::CloseDirective(
            directive.clone(),
            Box::new(info.clone()),
        ));
    }

    fn disjoint_directive(
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
}

impl PolyTypeConstraintInfo<TypeSystemInfo, Ty, TyVar> for TypeSystemInfo {
    fn instantiated_type_scheme(&mut self, scheme: &Scheme<Predicates<Ty, TyVar>, Ty, TyVar>) {
        self.info.push(Info::InstantiatedTypeScheme(scheme.clone()));
    }

    fn skolemized_type_scheme(
        &mut self,
        tys: &Vec<Ty>,
        scheme: &Scheme<Predicates<Ty, TyVar>, Ty, TyVar>,
    ) {
        self.info
            .push(Info::SkolemizedTypeScheme(tys.clone(), scheme.clone()));
    }
}

impl TypeSystemInfo {
    pub fn with_src(&mut self, src: Source) {
        self.source.push(src);
    }

    pub fn extend(&mut self, other: TypeSystemInfo) {
        self.info.extend(other.info);
        self.source.extend(other.source);
    }
}
