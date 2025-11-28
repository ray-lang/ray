use std::collections::VecDeque;

use ray_shared::pathlib::{Path, PathPart};

use crate::types::{Subst, Substitutable, TyVar};

impl Substitutable for Path {
    fn apply_subst(&mut self, subst: &Subst) {
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
}

#[cfg(test)]
mod tests {
    use ray_shared::pathlib::Path;

    use crate::types::{Subst, Substitutable, Ty, TyVar};

    #[test]
    fn path_apply_subst_basic() {
        let mut path = Path::from("T::[?t0,?t1]");
        let mut subst = Subst::new();
        subst.insert(TyVar::new("?t0"), Ty::uint());
        subst.insert(TyVar::new("?t1"), Ty::string());
        path.apply_subst(&subst);

        assert_eq!(&path.to_string(), "T::[uint,string]");
    }

    #[test]
    fn path_apply_subst_nested() {
        let mut path = Path::from("T");
        let args = vec!["list[?t0]", "set[?t1]"];
        path = path.append_type_args(args.into_iter());
        let mut subst = Subst::new();
        subst.insert(TyVar::new("?t0"), Ty::uint());
        subst.insert(TyVar::new("?t1"), Ty::string());
        path.apply_subst(&subst);

        assert_eq!(&path.to_string(), "T::[list[uint],set[string]]");
    }
}
