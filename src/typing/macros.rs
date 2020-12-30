macro_rules! cset {
    () => ( $crate::typing::ConstraintSet::new() );

    (@subtype $cs:ident $tv:ident $s:tt <: $($tail:tt)+) => {
        $cs.add($tv.clone(), $crate::typing::Constraint::Subtype($s, $crate::typing::ty::Ty::Var($tv.clone()), $($tail)+))
    };

    ($tv:ident => $($tail:tt)*) => {
        {
            let mut cs = $crate::typing::ConstraintSet::new();
            cset!(@subtype cs $tv $($tail)*);
            cs
        }
    };
}

#[macro_export]
macro_rules! mk_ctx {
    () => {
        $crate::typing::Ctx::new()
    };

    ( $( $tv:tt => $ty:expr ),+ $(, )? ) => {
        {
            let mut ctx = $crate::typing::Ctx::new();
            $(ctx.bind_var(stringify!($tv), $ty);)+
            ctx
        }
    };
}

#[macro_export]
macro_rules! add_binops {
    ($ctx:ident, [$($ops:expr),*], [$($tys:tt),*]) => {{
        add_binops!(@step $ctx, [$($ops),*], [$($tys),*]);
    }};
    (@step $ctx:ident, [$head_op:expr, $($tail_ops:expr),*], [$($tys:tt),*]) => {{
        add_binops!(@step $ctx, [$head_op], [$($tys),*]);
        add_binops!($ctx, [$($tail_ops),*], [$($tys),*]);
    }};
    (@step $ctx:ident, [$op:expr], [$($ty:tt),*]) => {{
        $($ctx.bind_var($op, mk_binop_ty!(Ty::$ty()));)*
    }};
    (@step $ctx:ident, [], []) => {};
}
#[macro_export]
macro_rules! mk_binop_ty {
    ($ty:expr) => {
        Ty::Func(vec![$ty, $ty], Box::new($ty))
    };
}

#[macro_export]
macro_rules! subst {
    () => {
        Subst::new()
    };

    ($k:expr => $v:expr) => {{
        let mut h = Subst::new();
        h.insert($k, $v);
        h
    }};
}

#[macro_export]
macro_rules! tvar {
    ($v:tt) => {
        TyVar(stringify!($v).to_string())
    };
}

#[macro_export]
macro_rules! mkexpr {
    (@mkty ('v $ty:tt)) => {
        $crate::typing::ty::Ty::Var($crate::typing::ty::TyVar(stringify!($ty).to_string()))
    };

    (@mkty $ty:tt) => {
        $crate::typing::ty::Ty::Projection(stringify!($ty).to_string(), vec![])
    };

    (fn $([ $($ty_param:ident),+ ])? ( $($arg:ident),+ ) => { $($body:tt)+ }) => {
        $crate::hir::HirNode::<()>::new($crate::hir::HirNodeKind::FunInf(
            vec![$( $($crate::typing::ty::TyVar(stringify!($ty_param).to_string())),+ )?],
            vec![$( $crate::hir::Param::new(stringify!($arg).to_string(), None) ),*],
            Box::new(mkexpr!($($body)+)),
        ))
    };

    (fn $([ $($ty_param:ident),+ ])? ( $($arg:ident:$ty:tt),* ) => { $($body:tt)+ }) => {
        $crate::hir::HirNode::<()>::new($crate::hir::HirNodeKind::Fun(
            vec![$( $(TyVar(stringify!($ty_param).to_string())),+ )?],
            vec![$((
                stringify!($arg).to_string(),
                mkexpr!(@ty $ty)
            )),*],
            Box::new(mkexpr!($($body)+)),
        ))
    };

    (let $x:ident = ($($head:tt)+) in ($($tail:tt)+)) => {
        $crate::hir::HirNode::<()>::new($crate::hir::HirNodeKind::Let(
            vec![(stringify!($x).to_string(), mkexpr!($($head)+))],
            Box::new(mkexpr!($($tail)+)),
        ))
    };

    (let ( $( $x:ident = ($($head:tt)+) ),+ ) in ($($tail:tt)+)) => {
        $crate::hir::HirNode::<()>::new($crate::hir::HirNodeKind::Let(
            vec![$(
                (stringify!($x).to_string(), mkexpr!($($head)+))
            ),+],
            Box::new(mkexpr!($($tail)+)),
        ))
    };

    ( $x:tt $([ $($ty_arg:tt),* ])? ($($arg:tt),*) ) => {
        $crate::hir::HirNode::<()>::new($crate::hir::HirNodeKind::Apply(
            Box::new(mkexpr!($x)),
            vec![$( $(mkexpr!(@mkty $ty_arg)),* )?],
            vec![$( mkexpr!($arg) ),*],
        ))
    };

    ($x:tt) => {
        $crate::hir::HirNode::<()>::new($crate::hir::HirNodeKind::Var(stringify!($x).to_string()))
    };
}

#[cfg(test)]
mod test {
    use crate::typing::ty::{Ty, TyVar};

    #[test]
    fn test_cset_macro() {
        let y = TyVar("'t0".to_string());
        let t = Ty::Var(TyVar("'t1".to_string()));
        let cs = cset! {
            y => (Ty::Never) <: t
        };

        println!("{:?}", cs);
    }

    #[test]
    fn test_mkexpr_macro() {
        let ex = mkexpr! {
            malloc[('v a)](1)
        };
        println!("{:#?}", ex);

        let ex = mkexpr! {
            let i = (malloc[int](1)) in (nil)
        };
        println!("{:#?}", ex);

        let ex = mkexpr! {
            let malloc = (fn [a] (size) => {()}) in (())
        };
        println!("{:#?}", ex);

        let ex = mkexpr! {
            let malloc = (fn [a] (size) => {
                let ptr = (int_to_ptr[('v a)](heap)) in
                (ptr)
            }) in (())
        };
        println!("{:#?}", ex);
    }
}
