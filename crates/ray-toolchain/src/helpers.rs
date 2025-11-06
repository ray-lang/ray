use std::{
    fs::{self, File},
    io::{BufReader, Read},
    path::Path,
};

use ray_cfg::ProjectCfg;
use sha2::Digest;

use crate::resolve::ToolchainSelector;

pub(crate) fn read_project_selector() -> anyhow::Result<Option<ToolchainSelector>> {
    let cfg = ProjectCfg::read()?; // your impl
    Ok(if let Some(p) = cfg.path {
        Some(ToolchainSelector::Path(p))
    } else if let Some(v) = cfg.version {
        Some(ToolchainSelector::Version(v))
    } else if let Some(c) = cfg.channel {
        Some(ToolchainSelector::Channel(c))
    } else {
        None
    })
}

pub(crate) fn copy_dir_contents(src: &Path, dst: &Path) -> anyhow::Result<()> {
    log::info!(
        "copying directory contents from {} to {}",
        src.display(),
        dst.display()
    );
    for entry in walkdir::WalkDir::new(src) {
        let entry = entry?;
        let rel = entry.path().strip_prefix(src)?;
        let target = dst.join(rel);
        if entry.file_type().is_dir() {
            log::info!("  creating directories {}", target.display());
            fs::create_dir_all(&target)?;
        } else {
            log::info!(
                "  copying {} to {}",
                entry.path().display(),
                target.display()
            );
            fs::copy(entry.path(), &target)?;
        }
    }
    Ok(())
}

pub(crate) fn extract_tar_zst(archive_path: &Path, dst: &Path) -> anyhow::Result<()> {
    log::info!(
        "extracting {} into {}",
        archive_path.display(),
        dst.display()
    );

    let file = File::open(archive_path)?;
    let decoder = zstd::Decoder::new(file)?;
    let mut archive = tar::Archive::new(decoder);
    archive.unpack(dst)?;

    // remove the original archive so it doesn't interfere with downstream
    // checks (and to avoid leaving stray files in the final toolchain)
    if std::fs::remove_file(archive_path).is_ok() {
        log::debug!("removed archive {} after unpacking", archive_path.display());
    }

    // Flatten single top-level folder if present (common in release tarballs)
    if let Ok(rd) = std::fs::read_dir(dst) {
        let mut entries = rd.flatten().collect::<Vec<_>>();
        // ignore any leftover non-directory files when considering flattening
        entries.retain(|entry| entry.file_type().map(|t| t.is_dir()).unwrap_or(false));
        if entries.len() == 1 {
            log::info!("flattening archive");
            let inner = entries.remove(0).path();
            let has_expected = inner.join("bin").exists() || inner.join("lib").exists();
            if has_expected {
                // Move contents up one level
                for e in std::fs::read_dir(&inner)?.flatten() {
                    let from = e.path();
                    let to = dst.join(e.file_name());
                    if from.is_dir() {
                        std::fs::create_dir_all(&to)?;
                        // shallow move: rename works if same fs; fallback to copy if needed later
                        std::fs::rename(&from, &to)?;
                    } else {
                        std::fs::rename(&from, &to)?;
                    }
                }
                std::fs::remove_dir_all(&inner)?;
            }
        }
    }

    Ok(())
}

pub(crate) fn download_file(url: &str, dest: &Path) -> anyhow::Result<()> {
    let mut resp = reqwest::blocking::get(url)?;
    if !resp.status().is_success() {
        anyhow::bail!("download failed: {} (HTTP {})", url, resp.status());
    }

    let mut out = File::create(dest)?;
    std::io::copy(&mut resp, &mut out)?;
    Ok(())
}

pub(crate) fn verify_sha256(file: &Path, expected: &str) -> anyhow::Result<()> {
    let mut f = BufReader::new(File::open(file)?);
    let mut hasher = sha2::Sha256::new();
    let mut buf = [0u8; 8192];
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let actual = format!("{:x}", hasher.finalize());
    if &actual != expected {
        anyhow::bail!("SHA256 mismatch: expected {}, got {}", expected, actual);
    }
    Ok(())
}
