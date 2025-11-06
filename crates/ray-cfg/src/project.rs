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
        let Some(path) = project_path() else {
            return Ok(ProjectCfg::default());
        };

        let raw = fs::read_to_string(path)?;
        Ok(toml::from_str(&raw)?)
    }
}

fn project_path() -> Option<std::path::PathBuf> {
    let mut dir = std::env::current_dir().expect("cwd");
    loop {
        let path = dir.join("ray.toml");
        if path.exists() {
            return Some(path);
        }

        if !dir.pop() {
            // nothing found
            return None;
        }
    }
}
