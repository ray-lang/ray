use std::{collections::HashMap, fmt::Display};

use crate::{
    InfoJoin, Predicates, TyVar,
    constraint::{InfoDetail, PolyTypeConstraintInfo, TypeConstraintInfo},
    types::{Predicate, Scheme, Ty},
    util::Join,
};

#[derive(Debug, Default, Clone)]
pub struct TopInfo {
    info: HashMap<String, String>,
}

impl Display for TopInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{\n")?;
        for (lhs, rhs) in self.info.iter() {
            write!(f, "  {} = {}\n", lhs, rhs)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl InfoJoin for TopInfo {
    fn join(mut self, other: Self) -> Self {
        self.info.extend(other.info);
        self
    }
}

impl InfoDetail for TopInfo {
    fn add_detail(&mut self, detail: &str) {
        self.info.insert("detail".to_string(), detail.to_string());
    }
}

impl<T, V> TypeConstraintInfo<TopInfo, T, V> for TopInfo
where
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn equality_type_pair(&mut self, lhs: &T, rhs: &T) {
        self.info.insert(
            "equality type pair".to_string(),
            format!("({}, {})", lhs, rhs),
        );
    }

    fn missing_predicate(&mut self, predicate: &Predicate<T, V>) {
        self.info
            .insert("missing predicate".to_string(), format!("{}", predicate));
    }

    fn ambiguous_predicate(&mut self, predicate: &Predicate<T, V>) {
        self.info
            .insert("ambiguous predicate".to_string(), format!("{}", predicate));
    }

    fn unsolved_predicate(&mut self, predicate: &Predicate<T, V>, info: &TopInfo) {
        self.info.insert(
            "unsolved predicate".to_string(),
            format!("({}, {})", predicate, info),
        );
    }

    fn predicate_arising_from(&mut self, predicate: &Predicate<T, V>) {
        self.info.insert(
            "predicate arising from".to_string(),
            format!("{}", predicate),
        );
    }

    fn parent_predicate(&mut self, predicate: &Predicate<T, V>) {
        self.info
            .insert("parent predicate".to_string(), format!("{}", predicate));
    }

    fn escaped_skolems(&mut self, skolems: &[V]) {
        self.info.insert(
            "escaped skolems".to_string(),
            format!("{}", skolems.join(", ")),
        );
    }

    fn never_directive(&mut self, predicate: &Predicate<T, V>, info: &TopInfo) {
        self.info.insert(
            "never directive".to_string(),
            format!("({}, {})", predicate, info),
        );
    }

    fn close_directive(&mut self, directive: &String, info: &TopInfo) {
        self.info.insert(
            "close directive".to_string(),
            format!("({}, {})", directive, info),
        );
    }

    fn disjoint_directive(
        &mut self,
        lhs: &String,
        lhs_info: &TopInfo,
        rhs: &String,
        rhs_info: &TopInfo,
    ) {
        self.info.insert(
            "disjoint directive".to_string(),
            format!("({}, {}) & ({}, {})", lhs, lhs_info, rhs, rhs_info),
        );
    }
}

impl<T, V> PolyTypeConstraintInfo<TopInfo, T, V> for TopInfo
where
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn instantiated_type_scheme(&mut self, scheme: &Scheme<Predicates<T, V>, T, V>) {
        let scheme = scheme.clone();
        self.info.insert(
            "instantiated type scheme".to_string(),
            format!("{}", scheme),
        );
    }

    fn skolemized_type_scheme(&mut self, tys: &Vec<T>, scheme: &Scheme<Predicates<T, V>, T, V>) {
        self.info.insert(
            "skolemized type scheme".to_string(),
            format!(
                "([{}], {})",
                tys.iter().map(|t| t.to_string()).join(", "),
                scheme
            ),
        );
    }
}

impl TopInfo {
    pub fn new(l: &str, r: &str) -> Self {
        let mut ret = TopInfo::default();
        ret.info.insert(l.to_string(), r.to_string());
        ret
    }

    pub fn add_info(&mut self, l: &str, r: &str) {
        self.info.insert(l.to_string(), r.to_string());
    }

    pub fn get(&self, l: &str) -> Option<&str> {
        self.info.get(l).map(|s| s.as_str())
    }

    pub fn iter(&self) -> std::collections::hash_map::Iter<'_, String, String> {
        self.info.iter()
    }
}
