use std::fs;
use toml_edit::{Item, Table};

use ray_cfg::RayConfig;

use crate::{
    ToolchainManager,
    helpers::{copy_dir_contents, download_file, extract_tar_zst, verify_sha256},
    resolve::ResolvedToolchain,
};

#[derive(Clone, Debug)]
pub enum InstallSource<'a> {
    PathDir(&'a std::path::Path), // already-unpacked dir
    PathTar(&'a std::path::Path), // .tar.zst or .tar.gz
    Url {
        url: &'a str,
        sha256: Option<&'a str>,
    }, // download and verify
}

#[derive(Clone, Debug)]
pub struct InstallSpec<'a> {
    pub root_path: std::path::PathBuf, // --root-path
    pub version: String,               // "0.1.0" or "nightly-2025-11-05" or "dev"
    pub triple: String,                // "wasm32-wasi"
    pub source: InstallSource<'a>,
    pub set_channel: Option<String>, // e.g. Some("stable") or None
    pub set_default: bool,
}

impl<'a> std::fmt::Display for InstallSource<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstallSource::PathDir(path) | InstallSource::PathTar(path) => {
                write!(f, "{}", path.display())
            }
            InstallSource::Url { url, .. } => write!(f, "{}", url),
        }
    }
}

impl ToolchainManager {
    pub fn install(spec: &InstallSpec) -> anyhow::Result<ResolvedToolchain> {
        let mode_label = match &spec.source {
            InstallSource::PathDir(_) => "directory",
            InstallSource::PathTar(_) => "archive",
            InstallSource::Url { .. } => "url",
        };
        log::info!("installing toolchain from {}", mode_label);
        log::info!("  root:    {}", spec.root_path.display());
        log::info!("  version: {}", spec.version);
        log::info!("  triple:  {}", spec.triple);
        log::info!("  source:  {}", spec.source);

        let toolchains_dir = spec.root_path.join("toolchains");
        let dest_root = toolchains_dir.join(&spec.version).join(&spec.triple);
        let tmp_dir = toolchains_dir.join(format!(".tmp-install-{}-{}", spec.version, spec.triple));
        if tmp_dir.exists() {
            fs::remove_dir_all(&tmp_dir)?;
        }
        fs::create_dir_all(&tmp_dir)?;

        match &spec.source {
            InstallSource::PathDir(src) => {
                copy_dir_contents(src, &tmp_dir)?;
            }
            InstallSource::PathTar(archive) => {
                log::info!("extracting toolchain archive...");
                extract_tar_zst(archive, &tmp_dir)?;
            }
            InstallSource::Url { url, sha256 } => {
                let tmp_file = tmp_dir.join("toolchain.tar.zst");
                log::info!("downloading toolchain archive from {}", url);
                download_file(url, &tmp_file)?;
                if let Some(expected) = sha256 {
                    verify_sha256(&tmp_file, expected)?;
                }

                log::info!("extracting toolchain archive...");
                extract_tar_zst(&tmp_file, &tmp_dir)?;
            }
        }

        // Move into final destination
        log::info!("installing toolchain into {}", dest_root.display());
        fs::create_dir_all(dest_root.parent().unwrap())?;
        if dest_root.exists() {
            fs::remove_dir_all(&dest_root)?;
        }
        fs::rename(&tmp_dir, &dest_root)?;

        let tc = ResolvedToolchain {
            root: dest_root.clone(),
            bin_dir: dest_root.join("bin"),
            lib_dir: dest_root.join("lib").join("ray"),
            version: spec.version.clone(),
            triple: spec.triple.clone(),
        };

        if !tc.bin_dir.exists() {
            anyhow::bail!(
                "toolchain missing bin/ directory at {}",
                tc.bin_dir.display()
            );
        }

        if !tc.lib_dir.exists() {
            anyhow::bail!(
                "toolchain missing lib/ray/ directory at {}",
                tc.lib_dir.display()
            );
        }

        let channel_to_set = spec
            .set_channel
            .clone()
            .or_else(|| match spec.version.as_str() {
                "stable" => Some(spec.version.clone()),
                _ => None,
            });

        if let Some(ch) = channel_to_set {
            ToolchainManager::set_channel(&spec.root_path, &ch, &tc)?;
        }

        if spec.set_default {
            ToolchainManager::set_default(&spec.root_path, &tc)?;
        }

        log::info!(
            "finished installing toolchain {}-{}",
            spec.version,
            spec.triple
        );
        Ok(tc)
    }

    pub fn set_channel(
        root: &std::path::Path,
        name: &str,
        tc: &ResolvedToolchain,
    ) -> anyhow::Result<()> {
        log::info!("updating channel mapping: {}", name);
        RayConfig::modify(root, |doc| {
            if !doc["default"].is_table() {
                doc["default"] = Item::Table(Table::new());
            }
            doc["default"]["channel"] = toml_edit::value(name);
            doc["default"]["target"] = toml_edit::value(&tc.triple);

            if !doc.contains_key("channels") || !doc["channels"].is_table() {
                let mut table = Table::new();
                table.set_implicit(true);
                doc["channels"] = Item::Table(table);
            }

            let channels = doc["channels"].as_table_mut().unwrap();
            if !channels.contains_key(name) || !channels[name].is_table() {
                channels[name] = Item::Table(Table::new());
            }

            channels[name]["version"] = toml_edit::value(&tc.version);
        })
    }

    pub fn set_default(root: &std::path::Path, tc: &ResolvedToolchain) -> anyhow::Result<()> {
        log::info!("setting default toolchain to {}", tc.version);
        RayConfig::modify(root, |doc| {
            if !doc["default"].is_table() {
                doc["default"] = Item::Table(Table::new());
            }
            doc["default"]["version"] = toml_edit::value(&tc.version);
            doc["default"]["target"] = toml_edit::value(&tc.triple);
        })
    }
}
