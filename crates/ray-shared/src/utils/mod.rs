mod traits;

pub use traits::*;

pub fn indent(s: String, n: usize) -> String {
    let mut dst = String::new();
    for (i, line) in s.lines().enumerate() {
        if i != 0 {
            dst.push('\n');
        }
        if line.len() != 0 {
            dst.push_str(&"  ".repeat(n));
            dst.push_str(line);
        }
    }
    dst
}

pub fn join<'a, T, S>(i: T, sep: S) -> String
where
    T: IntoIterator,
    T::Item: ToString,
    S: Into<&'a str>,
{
    i.into_iter()
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(sep.into())
}

pub fn map_join<'a, T, S, F>(i: T, sep: S, f: F) -> String
where
    T: IntoIterator,
    S: Into<&'a str>,
    F: Fn(T::Item) -> String,
{
    i.into_iter().map(f).collect::<Vec<_>>().join(sep.into())
}
