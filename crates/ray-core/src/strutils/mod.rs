pub fn indent_lines<S: std::fmt::Display>(s: S, n: usize) -> String {
    s.to_string()
        .lines()
        .map(|l| format!("{}{}", " ".repeat(n), l))
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn indent_lines_iter<T>(i: T, n: usize) -> String
where
    T: IntoIterator,
    T::Item: std::fmt::Display,
{
    i.into_iter()
        .flat_map(|item| {
            item.to_string()
                .lines()
                .map(|l| format!("{}{}", " ".repeat(n), l))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
        .join("\n")
}
