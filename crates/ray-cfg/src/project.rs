use std::fs;
use std::path;

use serde::Deserialize;

#[derive(Debug, Default, Clone, Deserialize)]
pub struct ProjectCfg {
    pub package: Option<PackageCfg>,
    pub toolchain: Option<ToolchainCfg>,
}

#[derive(Debug, Default, Clone, Deserialize)]
pub struct PackageCfg {
    pub name: Option<String>,
    pub version: Option<String>,
    #[serde(rename = "type")]
    pub package_type: Option<PackageType>,
    pub no_core: Option<bool>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PackageType {
    Lib,
    Bin,
}

#[derive(Debug, Default, Clone, Deserialize)]
pub struct ToolchainCfg {
    pub channel: Option<String>,
    pub version: Option<String>,
}

impl ProjectCfg {
    /// Read the project config from the current working directory.
    ///
    /// Returns a default (empty) config if no `ray.toml` exists in CWD.
    pub fn read() -> anyhow::Result<ProjectCfg> {
        let Some(path) = find_project_config() else {
            return Ok(ProjectCfg::default());
        };

        Self::read_from(&path)
    }

    /// Read the project config from a specific file path.
    pub fn read_from(path: &path::Path) -> anyhow::Result<ProjectCfg> {
        let raw = fs::read_to_string(path)?;
        Ok(toml::from_str(&raw)?)
    }

    /// Returns true if the package is configured as a library.
    pub fn is_lib(&self) -> bool {
        self.package
            .as_ref()
            .and_then(|p| p.package_type)
            .is_some_and(|t| t == PackageType::Lib)
    }

    /// Returns true if the package has `no_core = true`.
    pub fn no_core(&self) -> bool {
        self.package
            .as_ref()
            .and_then(|p| p.no_core)
            .unwrap_or(false)
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
