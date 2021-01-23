const ALPHABET: [char; 62] = [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i',
    'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 'A', 'B',
    'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U',
    'V', 'W', 'X', 'Y', 'Z',
];

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

pub fn rand_string(n: usize) -> String {
    let mut bytes = vec![0u8; n];
    for i in 0..n {
        bytes[i] = ALPHABET[(rand::random::<usize>() % ALPHABET.len())] as u8;
    }
    String::from_utf8(bytes).unwrap()
}
