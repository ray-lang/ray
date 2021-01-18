macro_rules! str {
    ($s:expr) => {
        $s.to_string()
    };
}

macro_rules! debug {
    ($($arg:tt)*) => (if cfg!(feature = "debug") { eprintln!($($arg)*) })
}

macro_rules! variant {
    ($x:expr, if $($p:ident)::+ ($($id:ident),*) , else |$e:ident| $b:block) => {{
        match $x {
            $($p)::+($($id),*) => ($($id),*),
            $e @ _ => $b,
        }
    }};

    ($x:expr, if $($p:ident)::+ ($($id:ident),*) , else $b:block) => {{
        match $x {
            $($p)::+($($id),*) => ($($id),*),
            _ => $b,
        }
    }};

    ($x:expr, if $($p:ident)::+ ($($id:ident),*)) => {{
        match $x {
            $($p)::+($($id),*) => ($($id),*),
            _ => panic!("Unexpected value found inside '{}'", stringify!($x)),
        }
    }};
}

macro_rules! aset {
    {} => ($crate::typing::top::assumptions::AssumptionSet::new());

    { $($e:tt : $v:tt),+ } => {{
        $crate::typing::top::assumptions::AssumptionSet::from(vec![
            $((stringify!($e).to_string(), Ty::Var(tvar!($v)))),*
        ])
    }};
}
