use serde::{Deserialize, Serialize};
use std::fs;
use toml_edit::{DocumentMut, Item, Table};

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
    pub requested_version: Option<String>,
    pub triple: String, // "wasm32-wasi"
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
        log::info!("  source:  {}", spec.source);

        let toolchains_dir = spec.root_path.join("toolchains");
        let tmp_dir = toolchains_dir.join(format!(".tmp-install-{}", std::process::id()));
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

        let manifest = match read_manifest(&tmp_dir) {
            Ok(m) => m,
            Err(err) => {
                log::warn!("failed to read manifest: {}", err);
                None
            }
        };

        let effective_version = manifest
            .as_ref()
            .map(|m| m.version.clone())
            .or_else(|| spec.requested_version.clone())
            .ok_or_else(|| {
                anyhow::anyhow!("toolchain version not specified in manifest or CLI arguments")
            })?;
        let effective_triple = manifest
            .as_ref()
            .map(|m| m.triple.clone())
            .unwrap_or_else(|| spec.triple.clone());
        let dest_root = toolchains_dir
            .join(&effective_version)
            .join(&effective_triple);

        log::info!("==> version: {}", effective_version);
        log::info!("==> triple:  {}", effective_triple);

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
            version: effective_version.clone(),
            triple: effective_triple.clone(),
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

        let manifest_channel = manifest.as_ref().map(|m| m.channel.clone());
        let channel_to_set = spec
            .set_channel
            .clone()
            .or(manifest_channel)
            .or_else(|| infer_channel_from_version(&effective_version));

        if let Some(ch) = channel_to_set {
            ToolchainManager::set_channel(&spec.root_path, &ch, &tc)?;
        }

        if spec.set_default {
            ToolchainManager::set_default(&spec.root_path, &tc)?;
        }

        log::info!(
            "finished installing toolchain {}-{}",
            effective_version,
            effective_triple
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

fn infer_channel_from_version(version: &str) -> Option<String> {
    if version == "stable" {
        Some("stable".to_string())
    } else if version == "nightly" || version.starts_with("nightly-") {
        Some("nightly".to_string())
    } else if version == "beta" || version.starts_with("beta-") {
        Some("beta".to_string())
    } else {
        None
    }
}

#[derive(Debug, Default, Clone, Deserialize)]
struct ToolchainManifest {
    version: String,
    channel: String,
    triple: String,
}

fn read_manifest(dir: &std::path::Path) -> anyhow::Result<Option<ToolchainManifest>> {
    let manifest_path = dir.join("manifest.toml");
    if !manifest_path.exists() {
        return Ok(None);
    }

    let contents = std::fs::read_to_string(&manifest_path)?;
    let tc = toml::from_str::<ToolchainManifest>(&contents)
        .map_err(|e| anyhow::anyhow!("parsing manifest.toml: {}", e))?;
    Ok(Some(tc))
}
