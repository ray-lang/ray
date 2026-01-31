#[macro_export]
macro_rules! str {
    ($s:expr) => {
        $s.to_string()
    };
    () => {
        "".to_string()
    };
}

#[macro_export]
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
