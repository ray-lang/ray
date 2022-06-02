use std::collections::HashMap;

use crate::{
    constraint::{InfoDetail, PolyTypeConstraintInfo, TypeConstraintInfo},
    types::{Predicate, Scheme, Ty},
    util::DisplayableVec,
};

#[derive(Debug, Default, Clone)]
pub struct TopInfo {
    info: HashMap<String, String>,
}

impl std::fmt::Display for TopInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{\n")?;
        for (lhs, rhs) in self.info.iter() {
            write!(f, "  {} = {}\n", lhs, rhs)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl InfoDetail for TopInfo {
    fn add_detail(&mut self, detail: &str) {
        self.info.insert("detail".to_string(), detail.to_string());
    }
}

impl TypeConstraintInfo<TopInfo> for TopInfo {
    fn equality_type_pair(&mut self, lhs: &Ty, rhs: &Ty) {
        self.info.insert(
            "equality type pair".to_string(),
            format!("({}, {})", lhs, rhs),
        );
    }

    fn ambiguous_predicate(&mut self, predicate: &Predicate) {
        self.info
            .insert("ambiguous predicate".to_string(), format!("{}", predicate));
    }

    fn unsolved_predicate(&mut self, predicate: &Predicate, info: &TopInfo) {
        self.info.insert(
            "unsolved predicate".to_string(),
            format!("({}, {})", predicate, info),
        );
    }

    fn predicate_arising_from(&mut self, predicate: &Predicate) {
        self.info.insert(
            "predicate arising from".to_string(),
            format!("{}", predicate),
        );
    }

    fn parent_predicate(&mut self, predicate: &Predicate) {
        self.info
            .insert("parent predicate".to_string(), format!("{}", predicate));
    }

    fn escaped_skolems(&mut self, skolems: &[u32]) {
        self.info
            .insert("escaped skolems".to_string(), format!("{:?}", skolems));
    }

    fn never_directive(&mut self, predicate: &Predicate, info: &TopInfo) {
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

impl PolyTypeConstraintInfo<TopInfo> for TopInfo {
    fn instantiated_type_scheme(&mut self, scheme: &Scheme<Vec<Predicate>>) {
        let scheme = scheme.clone();
        self.info.insert(
            "instantiated type scheme".to_string(),
            format!("{}", scheme.displayable()),
        );
    }

    fn skolemized_type_scheme(&mut self, tys: &Vec<Ty>, scheme: &Scheme<Vec<Predicate>>) {
        self.info.insert(
            "skolemized type scheme".to_string(),
            format!(
                "({}, {})",
                DisplayableVec::from(tys.clone()),
                scheme.displayable()
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

    pub fn iter(&self) -> std::collections::hash_map::Iter<String, String> {
        self.info.iter()
    }
}
