use ray_shared::pathlib::{Path, PathPart};

use crate::types::{Subst, Substitutable};

impl Substitutable for Path {
    fn apply_subst(&mut self, subst: &Subst) {
        for part in self.iter_mut() {
            match part {
                PathPart::Name(_) => { /* ignore */ }
                PathPart::TypeArgs(args) => args.apply_subst(subst),
                PathPart::Array(ty, _) => ty.apply_subst(subst),
                PathPart::FuncType(params, ret) => {
                    params.apply_subst(subst);
                    ret.apply_subst(subst);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ray_shared::{
        pathlib::Path,
        ty::{Ty, TyVar},
    };

    use crate::types::{Subst, Substitutable};

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
        let args = vec![
            Ty::proj("list", vec![Ty::var("?t0")]),
            Ty::proj("set", vec![Ty::var("?t1")]),
        ];
        path = path.append_type_args(args.iter());
        let mut subst = Subst::new();
        subst.insert(TyVar::new("?t0"), Ty::uint());
        subst.insert(TyVar::new("?t1"), Ty::string());
        path.apply_subst(&subst);

        assert_eq!(&path.to_string(), "T::[list[uint],set[string]]");
    }

    #[test]
    fn path_apply_subst_func_type_preserves_parens() {
        let mut path = Path::from("T::func");
        path = path.append_func_type(vec![Ty::unit()], Ty::string());
        let prev_str = path.to_string();
        let subst = Subst::new();
        path.apply_subst(&subst);
        let curr_str = path.to_string();
        assert_eq!(prev_str, curr_str);
    }

    #[test]
    fn path_apply_subst_func_type_preserves_multi_parens() {
        let mut path = Path::from("T::func");
        path = path.append_func_type(vec![Ty::unit(), Ty::unit()], Ty::unit());
        let prev_str = path.to_string();
        let subst = Subst::new();
        path.apply_subst(&subst);
        let curr_str = path.to_string();
        assert_eq!(prev_str, curr_str);
    }
    #[test]
    fn path_apply_subst_func_type_replaces_ret() {
        let mut path = Path::from("T::func");
        path = path.append_func_type(vec![Ty::i32(), Ty::i8()], Ty::var("?t0"));
        let mut subst = Subst::new();
        subst.insert(TyVar::new("?t0"), Ty::uint());
        path.apply_subst(&subst);
        let curr_str = path.to_string();
        assert_eq!(curr_str, "T::func::<(i32,i8):uint>");
    }

    #[test]
    fn path_apply_subst_func_type_replaces_typaram_in_ret() {
        let mut path = Path::from("T::func");
        path = path.append_func_type(
            vec![Ty::i32(), Ty::i8()],
            Ty::proj("list", vec![Ty::var("?t0")]),
        );
        let mut subst = Subst::new();
        subst.insert(TyVar::new("?t0"), Ty::uint());
        path.apply_subst(&subst);
        let curr_str = path.to_string();
        assert_eq!(curr_str, "T::func::<(i32,i8):list[uint]>");
    }
}
