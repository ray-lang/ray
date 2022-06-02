pub trait Join<Separator> {
    type Output;

    fn join(self, sep: Separator) -> Self::Output;
}

impl<I, S> Join<S> for I
where
    I: IntoIterator,
    I::Item: std::fmt::Display,
    S: std::fmt::Display,
{
    type Output = String;

    fn join(self, sep: S) -> Self::Output {
        let mut out = String::new();
        for (i, x) in self.into_iter().enumerate() {
            if i > 0 {
                out.push_str(&sep.to_string());
            }
            out.push_str(&x.to_string());
        }
        out
    }
}
