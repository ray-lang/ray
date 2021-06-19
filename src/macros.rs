macro_rules! str {
    ($s:expr) => {
        $s.to_string()
    };
}

macro_rules! unless {
    ($ex:expr, else $else_block:expr) => {
        match $ex {
            Some(x) => x,
            _ => $else_block,
        }
    };
    ($ex:expr) => {
        match $ex {
            Some(x) => x,
            _ => return,
        }
    };
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
