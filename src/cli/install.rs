use std::{path::PathBuf, process};

use clap::Args;
use ray_core::pathlib::RayPaths;
use ray_driver::GlobalOptions;
use ray_toolchain::{InstallSource, InstallSpec, ToolchainManager};

#[derive(Debug, Args)]
pub struct InstallOptions {
    #[arg(
        value_name = "CHANNEL|VERSION",
        help = "toolchain channel or version (defaults to manifest value when omitted)"
    )]
    pub channel_or_version: Option<String>,

    #[arg(
        long,
        value_name = "TRIPLE",
        default_value = "wasm32-wasi",
        help = "target triple to install"
    )]
    pub triple: String,

    #[arg(
        long,
        value_name = "DIR",
        conflicts_with_all = ["archive", "url"],
        help = "install from an already-unpacked directory"
    )]
    pub dir: Option<PathBuf>,

    #[arg(
        long,
        value_name = "ARCHIVE",
        conflicts_with_all = ["dir", "url"],
        help = "install from a local .tar or .tar.zst archive"
    )]
    pub archive: Option<PathBuf>,

    #[arg(
        long,
        value_name = "URL",
        conflicts_with_all = ["dir", "archive"],
        help = "download and install from a remote archive"
    )]
    pub url: Option<String>,

    #[arg(
        long,
        requires = "url",
        value_name = "SHA256",
        help = "expected SHA256 for the downloaded archive"
    )]
    pub sha256: Option<String>,

    #[arg(
        long,
        value_name = "CHANNEL",
        help = "update the named channel to point at the installed toolchain"
    )]
    pub set_channel: Option<String>,

    #[arg(
        long = "default",
        action = clap::ArgAction::SetTrue,
        help = "set the installed toolchain as the default version"
    )]
    pub set_default: bool,
}

pub(super) fn action(ray_paths: Option<RayPaths>, options: InstallOptions, globals: GlobalOptions) {
    let root_path = if let Some(paths) = ray_paths {
        paths.get_root().as_ref().to_path_buf()
    } else if let Some(explicit) = globals.root_path.as_ref() {
        explicit.as_ref().to_path_buf()
    } else {
        RayPaths::bootstrap_root().get_root().as_ref().to_path_buf()
    };

    if !root_path.exists() {
        if let Err(err) = std::fs::create_dir_all(&root_path) {
            log::error!(
                "failed to create toolchain root at {}: {}",
                root_path.display(),
                err
            );
            process::exit(1);
        }
        log::info!("created toolchain root at {}", root_path.display());
    }

    let source = if let Some(dir) = options.dir.as_ref() {
        InstallSource::PathDir(dir.as_path())
    } else if let Some(archive) = options.archive.as_ref() {
        InstallSource::PathTar(archive.as_path())
    } else if let Some(url) = options.url.as_deref() {
        InstallSource::Url {
            url,
            sha256: options.sha256.as_deref(),
        }
    } else {
        log::error!("specify one of --dir, --archive, or --url as the install source");
        process::exit(1);
    };

    let spec = InstallSpec {
        root_path,
        requested_version: options.channel_or_version.clone(),
        triple: options.triple.clone(),
        source,
        set_channel: options.set_channel.clone(),
        set_default: options.set_default,
    };

    if let Err(err) = ToolchainManager::install(&spec) {
        log::error!("{}", err);
        for cause in err.chain().skip(1) {
            log::error!("caused by: {}", cause);
        }
        process::exit(1);
    }
}
