use std::fs;

use serde::Deserialize;

#[derive(Debug, Default, Clone, Deserialize)]
pub struct ProjectCfg {
    pub channel: Option<String>,
    pub version: Option<String>,
    pub path: Option<std::path::PathBuf>,
}

impl ProjectCfg {
    pub fn read() -> anyhow::Result<ProjectCfg> {
        let Some(path) = find_project_config() else {
            return Ok(ProjectCfg::default());
        };

        let raw = fs::read_to_string(path)?;
        Ok(toml::from_str(&raw)?)
    }
}

/// Look for `ray.toml` in the current working directory.
///
/// Returns the full path to `ray.toml` if it exists in CWD, or `None`.
/// Does NOT walk up parent directories — the file must be in the exact CWD.
pub fn find_project_config() -> Option<std::path::PathBuf> {
    let path = std::env::current_dir().ok()?.join("ray.toml");
    path.exists().then_some(path)
}
