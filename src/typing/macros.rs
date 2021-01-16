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
    {} => {
        $crate::typing::Subst::new()
    };

    { $($key:expr => $value:expr),+ $(,)? } => {
        {
            let mut s = $crate::typing::Subst::new();
            $(
                s.insert($key, $value);
            )+
            s
        }
    };
}

#[macro_export]
macro_rules! tvar {
    ($v:tt) => {
        $crate::typing::ty::TyVar($crate::ast::Path::from(stringify!($v)))
    };
}

#[macro_export]
macro_rules! mkexpr {
    (@mkty ('v $ty:tt)) => {
        $crate::typing::ty::Ty::Var($crate::typing::ty::TyVar($crate::ast::Path::from(stringify!($ty))))
    };

    (@mkty $ty:tt) => {
        $crate::typing::ty::Ty::Projection(stringify!($ty).to_string(), vec![])
    };

    (fn ( $($arg:ident),+ ) => { $($body:tt)+ }) => {
        $crate::hir::HirNode::new($crate::hir::HirNodeKind::Fun(
            vec![$( $crate::hir::Param::new(stringify!($arg).to_string(), None) ),*],
            Box::new(mkexpr!($($body)+)),
        ))
    };

    (fn ( $($arg:ident:$ty:tt),* ) => { $($body:tt)+ }) => {
        $crate::hir::HirNode::new($crate::hir::HirNodeKind::Fun(
            vec![$((
                stringify!($arg).to_string(),
                mkexpr!(@ty $ty)
            )),*],
            Box::new(mkexpr!($($body)+)),
        ))
    };

    (let $x:ident = ($($head:tt)+) in ($($tail:tt)+)) => {
        $crate::hir::HirNode::new($crate::hir::HirNodeKind::Let(
            vec![$crate::hir::HirDecl::var(stringify!($x).to_string(), mkexpr!($($head)+))],
            Box::new(mkexpr!($($tail)+)),
        ))
    };

    (let ( $( $x:ident = ($($head:tt)+) ),+ ) in ($($tail:tt)+)) => {
        $crate::hir::HirNode::new($crate::hir::HirNodeKind::Let(
            vec![$(
                (stringify!($x).to_string(), mkexpr!($($head)+))
            ),+],
            Box::new(mkexpr!($($tail)+)),
        ))
    };

    ( $x:tt $([ $($ty_arg:tt),* ])? ($($arg:tt),*) ) => {
        $crate::hir::HirNode::new($crate::hir::HirNodeKind::Apply(
            Box::new(mkexpr!($x)),
            vec![$( $(mkexpr!(@mkty $ty_arg)),* )?],
            vec![$( mkexpr!($arg) ),*],
        ))
    };

    ($x:tt) => {
        $crate::hir::HirNode::new($crate::hir::HirNodeKind::Var(stringify!($x).to_string()))
    };
}
