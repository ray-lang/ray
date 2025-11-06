use std::str::FromStr;

#[derive(Debug, Copy, Clone)]
pub enum OptLevel {
    O0,
    O1,
    O2,
    O3,
    Os,
    Oz,
}

impl Default for OptLevel {
    fn default() -> Self {
        OptLevel::O2
    }
}

impl std::fmt::Display for OptLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.into();
        write!(f, "{}", s)
    }
}

impl Into<String> for &OptLevel {
    fn into(self) -> String {
        match self {
            OptLevel::O0 => "0".into(),
            OptLevel::O1 => "1".into(),
            OptLevel::O2 => "2".into(),
            OptLevel::O3 => "3".into(),
            OptLevel::Os => "s".into(),
            OptLevel::Oz => "z".into(),
        }
    }
}

impl FromStr for OptLevel {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "0" => OptLevel::O0,
            "1" => OptLevel::O1,
            "2" => OptLevel::O2,
            "3" => OptLevel::O3,
            "s" => OptLevel::Os,
            "z" => OptLevel::Oz,
            _ => OptLevel::O2,
        })
    }
}
