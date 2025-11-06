use ray_cfg::RayConfig;

use crate::{ToolchainManager, helpers::read_project_selector};

#[derive(Clone, Debug)]
pub enum ToolchainSelector {
    Channel(String),          // "stable", "nightly", "dev"
    Version(String),          // "0.1.0"
    Path(std::path::PathBuf), // explicit dir
    Auto,                     // let resolver choose by precedence
}

#[derive(Clone, Debug)]
pub struct ResolveSpec {
    pub root_path: std::path::PathBuf, // from --root-path
    pub selector: ToolchainSelector,   // built by CLI layer
    pub target: Option<String>,        // default "wasm32-wasi" if None
    pub allow_flat_fallback: bool,     // keep true to support current .ray
}

#[derive(Clone, Debug)]
pub struct ResolvedToolchain {
    pub root: std::path::PathBuf, // concrete toolchain dir
    pub bin_dir: std::path::PathBuf,
    pub lib_dir: std::path::PathBuf,
    pub version: String, // "0.1.0" or channel name or "dev-flat"
    pub triple: String,  // "wasm32-wasi"
}

impl ResolvedToolchain {
    pub(crate) fn try_from_selector(
        root: &std::path::Path,
        selector: &ToolchainSelector,
        triple: &str,
    ) -> anyhow::Result<Option<ResolvedToolchain>> {
        match selector {
            ToolchainSelector::Path(p) => Ok(Some(ResolvedToolchain::try_from_path(p, triple)?)),
            ToolchainSelector::Version(v) => ResolvedToolchain::try_version(root, &v, triple),
            ToolchainSelector::Channel(c) => ResolvedToolchain::try_channel(root, &c, triple),
            ToolchainSelector::Auto => Ok(None),
        }
    }

    pub(crate) fn try_from_path(
        dir: &std::path::Path,
        triple: &str,
    ) -> anyhow::Result<ResolvedToolchain> {
        let tc = if dir.join("bin").exists() {
            dir.to_path_buf()
        } else {
            dir.join(triple)
        };
        Ok(ResolvedToolchain {
            root: tc.clone(),
            bin_dir: tc.join("bin"),
            lib_dir: tc.join("lib").join("ray"),
            version: "path".into(),
            triple: triple.into(),
        })
    }

    pub(crate) fn try_version(
        root: &std::path::Path,
        v: &str,
        triple: &str,
    ) -> anyhow::Result<Option<ResolvedToolchain>> {
        let p = root.join("toolchains").join(v).join(triple);
        Ok(if p.exists() {
            Some(ResolvedToolchain {
                root: p.clone(),
                bin_dir: p.join("bin"),
                lib_dir: p.join("lib").join("ray"),
                version: v.into(),
                triple: triple.into(),
            })
        } else {
            None
        })
    }

    pub(crate) fn try_channel(
        root: &std::path::Path,
        name: &str,
        triple: &str,
    ) -> anyhow::Result<Option<ResolvedToolchain>> {
        let p = root.join("channels").join(name);
        Ok(if p.exists() {
            Some(ResolvedToolchain {
                root: p.clone(),
                bin_dir: p.join("bin"),
                lib_dir: p.join("lib").join("ray"),
                version: name.into(),
                triple: triple.into(),
            })
        } else {
            None
        })
    }

    pub(crate) fn try_from_env(
        root: &std::path::Path,
        triple: &str,
    ) -> anyhow::Result<Option<ResolvedToolchain>> {
        if let Ok(path) = std::env::var("RAY_TOOLCHAIN_PATH") {
            return Ok(Some(ResolvedToolchain::try_from_path(
                std::path::Path::new(&path),
                triple,
            )?));
        }

        if let Ok(v) = std::env::var("RAY_TOOLCHAIN_VERSION") {
            if let Some(tc) = ResolvedToolchain::try_version(root, &v, triple)? {
                return Ok(Some(tc));
            }
        }

        if let Ok(ch) = std::env::var("RAY_CHANNEL") {
            // Resolve channel via config mapping; fall back to treating it as a version.
            let cfg = RayConfig::load(root)?;
            let ver = cfg
                .channels
                .get(&ch)
                .and_then(|c| c.version.as_ref())
                .cloned()
                .unwrap_or(ch);
            if let Some(tc) = ResolvedToolchain::try_version(root, &ver, triple)? {
                return Ok(Some(tc));
            }
        }

        Ok(None)
    }

    pub(crate) fn try_from_config(
        root: &std::path::Path,
        triple: &str,
    ) -> anyhow::Result<Option<ResolvedToolchain>> {
        let cfg = RayConfig::load(root)?;
        let target = cfg
            .default
            .target
            .as_ref()
            .map(|c| c.as_str())
            .unwrap_or(triple);

        let version = if let Some(version) = &cfg.default.version {
            version.clone()
        } else if let Some(channel) = &cfg.default.channel {
            cfg.channels
                .get(channel)
                .and_then(|c| c.version.as_ref())
                .unwrap_or(channel)
                .clone()
        } else {
            return Ok(None);
        };

        let tc = root.join("toolchains").join(&version).join(target);
        if tc.exists() {
            return Ok(Some(ResolvedToolchain {
                root: tc.clone(),
                bin_dir: tc.join("bin"),
                lib_dir: tc.join("lib").join("ray"),
                version,
                triple: target.to_string(),
            }));
        }
        Ok(None)
    }
}

impl ToolchainManager {
    pub fn resolve(spec: &ResolveSpec) -> anyhow::Result<ResolvedToolchain> {
        let root = &spec.root_path;
        let triple = if let Some(t) = &spec.target {
            t.clone()
        } else {
            // Consult global config for default target; fall back to wasm32-wasi.
            match RayConfig::load(root) {
                Ok(cfg) => cfg.default.target.unwrap_or_else(|| "wasm32-wasi".into()),
                Err(_) => "wasm32-wasi".into(),
            }
        };

        // Explicit override
        if let Some(tc) = ResolvedToolchain::try_from_selector(root, &spec.selector, &triple)? {
            return Ok(tc);
        }

        // Project manifest
        if let Some(selector) = read_project_selector()? {
            if let Some(tc) = ResolvedToolchain::try_from_selector(root, &selector, &triple)? {
                return Ok(tc);
            }
        }

        // Environment
        if let Some(tc) = ResolvedToolchain::try_from_env(root, &triple)? {
            return Ok(tc);
        }

        // Global config
        if let Some(tc) = ResolvedToolchain::try_from_config(root, &triple)? {
            return Ok(tc);
        }

        // Stable
        if let Some(tc) = ResolvedToolchain::try_channel(root, "stable", &triple)? {
            return Ok(tc);
        }

        // Flat fallback
        if spec.allow_flat_fallback {
            if root.join("bin").exists() {
                return Ok(ResolvedToolchain {
                    root: root.clone(),
                    bin_dir: root.join("bin"),
                    lib_dir: root.join("lib").join("ray"),
                    version: "dev-flat".into(),
                    triple,
                });
            }
        }

        anyhow::bail!("No toolchain found under {}", root.display());
    }
}
