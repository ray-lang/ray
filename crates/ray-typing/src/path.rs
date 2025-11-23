use std::collections::VecDeque;

use crate::top::{Subst, Substitutable};
use ray_shared::pathlib::{Path, PathPart};

use super::ty::{Ty, TyVar};

impl Substitutable<TyVar, Ty> for Path {
    fn apply_subst(&mut self, subst: &Subst<TyVar, Ty>) {
        let mut parts = VecDeque::new();
        for part in self.drain(..).into_iter() {
            if let PathPart::FuncType(func_ty) = part {
                let s = func_ty.trim_matches(|ch| ch == '<' || ch == '>');
                let mut args = String::new();
                let mut ret = String::new();
                let mut paren_stack = 0;
                let mut is_args = true;
                for ch in s.chars() {
                    if is_args {
                        match ch {
                            '(' => {
                                paren_stack += 1;
                                continue;
                            }
                            ')' => {
                                paren_stack -= 1;
                                continue;
                            }
                            ':' if paren_stack == 0 => {
                                is_args = false;
                                continue;
                            }
                            _ => (),
                        }
                    }

                    if is_args {
                        args.push(ch);
                    } else {
                        ret.push(ch);
                    }
                }

                let args = args
                    .split(',')
                    .map(|a| {
                        let tv = TyVar(Path::from(a));
                        if let Some(ty) = subst.get(&tv) {
                            ty.clone().to_string()
                        } else {
                            a.to_string()
                        }
                    })
                    .collect::<Vec<_>>();
                let ret = {
                    let tv = TyVar(Path::from(ret.as_str()));
                    if let Some(ty) = subst.get(&tv) {
                        ty.clone().to_string()
                    } else {
                        ret
                    }
                };
                parts.push_back(PathPart::FuncType(format!(
                    "<({}):{}>",
                    args.join(","),
                    ret
                )));
            } else if let PathPart::TypeArgs(args) = part {
                let args = args
                    .trim_matches(|ch| ch == '[' || ch == ']')
                    .split(',')
                    .map(|a| {
                        let tv = TyVar(Path::from(a));
                        if let Some(ty) = subst.get(&tv) {
                            ty.clone().to_string()
                        } else {
                            a.to_string()
                        }
                    })
                    .collect::<Vec<_>>();
                let args = format!("[{}]", args.join(","));
                log::debug!("[Path::apply_subst] args: {}", args);
                parts.push_back(PathPart::TypeArgs(args));
            } else {
                parts.push_back(part);
                let tv = TyVar(Path::from(parts.clone()));
                if let Some(ty) = subst.get(&tv) {
                    parts = ty
                        .to_string()
                        .split("::")
                        .map(|s| PathPart::Name(s.to_string()))
                        .collect::<VecDeque<_>>();
                }
            }
        }

        *self = Path::from(parts)
    }

    fn apply_subst_all(&mut self, subst: &Subst<TyVar, Ty>) {
        self.apply_subst(subst);
    }

    fn free_vars(&self) -> Vec<&TyVar> {
        vec![]
    }
}
