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

pub trait FoldFirst {
    type Item;

    fn foldf<F>(self, f: F) -> Option<Self::Item>
    where
        F: FnMut(Self::Item, Self::Item) -> Self::Item,
        Self: Sized;
}

impl<I: Iterator> FoldFirst for I {
    type Item = I::Item;

    fn foldf<F>(mut self, mut f: F) -> Option<Self::Item>
    where
        F: FnMut(Self::Item, Self::Item) -> Self::Item,
        Self: Sized,
    {
        if let Some(mut curr) = self.next() {
            while let Some(next) = self.next() {
                curr = f(curr, next);
            }

            Some(curr)
        } else {
            None
        }
    }
}
