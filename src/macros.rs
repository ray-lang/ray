macro_rules! str {
    ($s:expr) => {
        $s.to_string()
    };
}

macro_rules! debug {
    ($($arg:tt)*) => (if cfg!(feature = "debug") { eprintln!($($arg)*) })
}

macro_rules! variant {
    // Internal Variants
    (@tuple [$(,)*], [$($ids:ident)*], $($p:ident)::+, $t:expr) => {
        match $t {
            $($p)::+ ( $($ids),* ) => Some(( $($ids),* )),
            _ => None,
        }
    };
    (@tuple [$(,)*], [$($ids:ident)*], $($p:ident)::+, $t:expr, $else_branch:expr) => {
        match $t {
            $($p)::+ ( $($ids),* ) => ( $($ids),* ),
            _ => $else_branch,
        }
    };
    (@tuple [_], [$($ids:ident)*], $($p:ident)::+, $t:expr $(, $else_branch:expr)?) => {
        variant!(@tuple [], [$($ids)* x], $($p)::+, $t $(, $else_branch)?)
    };
    (@tuple [_, $($more:tt)*], [$($ids:ident)*], $($p:ident)::+, $t:expr $(, $else_branch:expr)?) => {
        variant!(@tuple [$($more)*], [$($ids)* x], $($p)::+, $t $(, $else_branch)?)
    };

    // Struct Variants
    ($($p:ident)::+ { $($i:ident),* $(,)* } , $t:expr) => {
        match $t {
            $($p)::+ {$($i),*} => Some(($($i),*)),
            _ => None
        }
    };

    // Tuple Variants
    ($($p:ident)::+ ( $($its:tt)* ) , $t:expr $(, else $else_branch:expr )?) => {
        variant!(@tuple [$($its)*], [], $($p)::+, $t $(, $else_branch)?)
    };
}

macro_rules! aset {
    {} => ($crate::typing::top::assumptions::AssumptionSet::new());

    { $($e:tt : $v:tt),+ } => {{
        $crate::typing::top::assumptions::AssumptionSet::from(vec![
            $((stringify!($e).to_string(), Ty::Var(tvar!($v)))),*
        ])
    }};
}
