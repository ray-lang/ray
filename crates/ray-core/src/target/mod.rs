use std::fmt;
use std::str::FromStr;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum WasiFlavor {
    /// Legacy target triple used by older toolchains (pre-WASI Preview 1).
    Legacy,
    /// Default triple for modern toolchains (WASI Preview 1).
    Wasip1,
    /// WASI Preview 1 with threads enabled.
    Wasip1Threads,
    /// WASI Preview 2 experimental triple.
    Wasip2,
}

impl WasiFlavor {
    pub fn triple(self) -> &'static str {
        match self {
            WasiFlavor::Legacy => "wasm32-wasi",
            WasiFlavor::Wasip1 => "wasm32-wasip1",
            WasiFlavor::Wasip1Threads => "wasm32-wasip1-threads",
            WasiFlavor::Wasip2 => "wasm32-wasip2",
        }
    }
}

impl Default for WasiFlavor {
    fn default() -> Self {
        WasiFlavor::Wasip1
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Target {
    /// Alias for the plain wasm32 target without WASI.
    Wasm32,
    /// Any of the supported WASI target triples.
    Wasm32Wasi(WasiFlavor),
}

impl Target {
    #[allow(dead_code)]
    pub fn available() -> Vec<Target> {
        vec![
            Target::Wasm32,
            Target::Wasm32Wasi(WasiFlavor::Wasip1),
            Target::Wasm32Wasi(WasiFlavor::Wasip1Threads),
            Target::Wasm32Wasi(WasiFlavor::Wasip2),
            Target::Wasm32Wasi(WasiFlavor::Legacy),
        ]
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Target::Wasm32 => "wasm32",
            Target::Wasm32Wasi(flavor) => flavor.triple(),
        }
    }

    pub fn is_wasi(&self) -> bool {
        matches!(self, Target::Wasm32Wasi(_))
    }

    pub fn lld_flavor(&self) -> &'static str {
        match self {
            Target::Wasm32 => "wasm",
            Target::Wasm32Wasi(_) => "wasm",
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
        let normalized = s.trim().to_ascii_lowercase();
        match normalized.as_str() {
            "wasm" | "wasm32" => Ok(Target::Wasm32),
            "wasi" => Ok(Target::Wasm32Wasi(WasiFlavor::default())),
            "wasm32-wasi" => Ok(Target::Wasm32Wasi(WasiFlavor::Legacy)),
            "wasm32-wasip1" => Ok(Target::Wasm32Wasi(WasiFlavor::Wasip1)),
            "wasm32-wasip1-threads" => Ok(Target::Wasm32Wasi(WasiFlavor::Wasip1Threads)),
            "wasm32-wasip2" => Ok(Target::Wasm32Wasi(WasiFlavor::Wasip2)),
            _ => Err(format!("{} is not a valid target", s)),
        }
    }
}

impl Default for Target {
    fn default() -> Target {
        Target::Wasm32Wasi(WasiFlavor::default())
    }
}
