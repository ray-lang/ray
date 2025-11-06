use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, path::Path};

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RayConfig {
    #[serde(default)]
    pub default: DefaultConfig,
    #[serde(default)]
    pub channels: HashMap<String, ChannelConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DefaultConfig {
    pub version: Option<String>,
    pub channel: Option<String>,
    pub target: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ChannelConfig {
    pub version: Option<String>,
}

impl RayConfig {
    pub fn load(root: &Path) -> Result<RayConfig> {
        let p = root.join("config.toml");
        if !p.exists() {
            return Ok(RayConfig::default());
        }
        let text =
            std::fs::read_to_string(&p).with_context(|| format!("reading {}", p.display()))?;
        let cfg: RayConfig =
            toml::from_str(&text).with_context(|| format!("parsing {}", p.display()))?;
        Ok(cfg)
    }

    pub fn modify(root: &Path, mutate: impl FnOnce(&mut toml_edit::DocumentMut)) -> Result<()> {
        let p = root.join("config.toml");
        let doc = if p.exists() {
            let text = std::fs::read_to_string(&p)?;
            text.parse::<toml_edit::DocumentMut>()
                .with_context(|| format!("parsing {} with toml_edit", p.display()))?
        } else {
            // create a minimal skeleton
            "[default]\n".parse::<toml_edit::DocumentMut>().unwrap()
        };
        let mut doc = doc;
        mutate(&mut doc);
        std::fs::write(&p, doc.to_string())?;
        Ok(())
    }
}
