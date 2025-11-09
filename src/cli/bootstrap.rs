use std::{
    fs::File,
    io::{self, Write},
    path::Path,
};

use anyhow::{Context, Result};
use clap::Args;
use flate2::read::GzDecoder;
use ray_core::pathlib::RayPaths;
use serde::Deserialize;
use tempfile::Builder as TempDirBuilder;

#[derive(Debug, Args)]
pub struct BootstrapOptions {
    #[arg(
        value_name = "TAG",
        help = "Release tag to install (nightly-YYYY-MM-DD, v0.x.y, etc.). Defaults to latest."
    )]
    pub tag: Option<String>,
}

pub(super) fn action(target_root: RayPaths, options: BootstrapOptions) -> Result<()> {
    let release_tag = match options.tag {
        Some(tag) => tag,
        None => resolve_latest_tag()?,
    };

    let toolchain_asset = format!("ray-toolchain-{release_tag}.tar.gz");
    let download_url = format!(
        "https://github.com/ray-lang/ray/releases/download/{release_tag}/{toolchain_asset}"
    );

    let tempdir = TempDirBuilder::new()
        .prefix("ray-bootstrap-")
        .tempdir()
        .context("failed to create temporary directory")?;
    let archive_path = tempdir.path().join(&toolchain_asset);

    println!("==> downloading {toolchain_asset}");
    download_to_path(&download_url, &archive_path)?;

    let target_path = target_root.get_root();
    std::fs::create_dir_all(target_path.as_ref())
        .with_context(|| format!("failed to create {}", target_path))?;

    println!(
        "==> extracting toolchain into {}",
        target_path.as_ref().display()
    );
    extract_archive(&archive_path, target_path.as_ref())?;

    println!();
    println!("Ray toolchain installed!");
    println!("  root path: {}", target_path);

    Ok(())
}

fn resolve_latest_tag() -> Result<String> {
    #[derive(Deserialize)]
    struct Release {
        tag_name: String,
    }

    println!("==> detecting latest Ray release");
    let agent: ureq::Agent = ureq::Agent::config_builder()
        .user_agent("ray-bootstrap")
        .build()
        .into();

    let mut response = agent
        .get("https://api.github.com/repos/ray-lang/ray/releases/latest")
        .call()
        .context("failed to query GitHub for the latest release")?;

    let release: Release = response
        .body_mut()
        .read_json()
        .context("failed to parse GitHub release response")?;

    if release.tag_name.trim().is_empty() {
        anyhow::bail!("GitHub API returned an empty release tag");
    }

    Ok(release.tag_name)
}

fn download_to_path(url: &str, dest: &Path) -> Result<()> {
    let agent: ureq::Agent = ureq::Agent::config_builder()
        .user_agent("ray-bootstrap")
        .build()
        .into();
    let response = agent
        .get(url)
        .call()
        .with_context(|| format!("failed to download {url}"))?;

    let mut file =
        File::create(dest).with_context(|| format!("failed to create {}", dest.display()))?;

    let mut reader = response.into_body().into_reader();
    io::copy(&mut reader, &mut file)
        .with_context(|| format!("failed to write {}", dest.display()))?;
    file.flush()
        .with_context(|| format!("failed to flush {}", dest.display()))?;
    Ok(())
}

fn extract_archive(archive: &Path, destination: &Path) -> Result<()> {
    let file =
        File::open(archive).with_context(|| format!("failed to open {}", archive.display()))?;
    let decoder = GzDecoder::new(file);
    let mut bundle = tar::Archive::new(decoder);
    bundle
        .unpack(destination)
        .with_context(|| format!("failed to unpack into {}", destination.display()))?;
    Ok(())
}
