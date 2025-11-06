use std::{
    ffi::{OsStr, OsString},
    process::Stdio,
};

use ray_core::pathlib::RayPaths;

pub(crate) fn run_backend<C: AsRef<OsStr>>(
    ray_paths: RayPaths,
    subcmd: C,
    argv: Vec<OsString>,
) -> () {
    let bin_path = ray_paths.get_backend_path();
    let mut cmd = std::process::Command::new(bin_path.to_string());
    cmd.arg(subcmd).args(argv);

    let result = cmd
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status();

    match result {
        Ok(status) => {
            if !status.success() {
                std::process::exit(status.code().unwrap_or(1));
            }
        }
        Err(err) => {
            log::error!("{}", err)
        }
    }
}
