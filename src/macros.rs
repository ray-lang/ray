macro_rules! str {
    ($s:expr) => {
        $s.to_string()
    };
}

macro_rules! debug {
    ($($arg:tt)*) => (if cfg!(feature = "debug") { eprintln!($($arg)*) })
}
