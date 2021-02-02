use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Modifier {
    /// pub
    Pub,
    /// static
    Static,
    /// hidden
    Hidden,
    /// internal
    Internal,
    /// unsafe
    Unsafe,
    /// wasi
    Wasi,
}

impl fmt::Display for Modifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<S: AsRef<str>> From<S> for Modifier {
    fn from(s: S) -> Modifier {
        match s.as_ref() {
            "pub" => Modifier::Pub,
            "static" => Modifier::Static,
            "hidden" => Modifier::Hidden,
            "internal" => Modifier::Internal,
            "unsafe" => Modifier::Unsafe,
            "wasi" => Modifier::Wasi,
            _ => unreachable!(),
        }
    }
}

impl Modifier {
    fn as_str(&self) -> &'static str {
        match self {
            Modifier::Pub => "pub",
            Modifier::Static => "static",
            Modifier::Hidden => "hidden",
            Modifier::Internal => "internal",
            Modifier::Unsafe => "unsafe",
            Modifier::Wasi => "wasi",
        }
    }
}
