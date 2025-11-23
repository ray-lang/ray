#[macro_export]
macro_rules! str {
    ($s:expr) => {
        $s.to_string()
    };
    () => {
        "".to_string()
    };
}
