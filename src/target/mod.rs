use std::fmt;
use std::str::FromStr;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Target {
    Wasm, // this is just an alias for Wasm32
    Wasm32,
    Wasi, // this is just an alias for Wasm32Wasi
    Wasm32Wasi,
}

impl Target {
    #[allow(dead_code)]
    pub fn available() -> Vec<Target> {
        vec![
            Target::Wasm32,
            Target::Wasm32Wasi,
            Target::Wasi,
            Target::Wasm,
        ]
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Target::Wasm32Wasi => "wasm32-wasi",
            Target::Wasi => "wasi",
            Target::Wasm32 => "wasm32",
            Target::Wasm => "wasm",
        }
    }
}

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for Target {
    type Err = String;

    fn from_str(s: &str) -> Result<Target, Self::Err> {
        match s {
            "wasm" | "wasm32" => Ok(Target::Wasm32),
            "wasi" | "wasm32-wasi" => Ok(Target::Wasm32Wasi),
            _ => Err(format!("{} is not a valid target", s)),
        }
    }
}

impl Default for Target {
    fn default() -> Target {
        Target::Wasm32Wasi
    }
}
