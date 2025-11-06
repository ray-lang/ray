use std::{
    env,
    ffi::{OsStr, OsString},
    path::Path,
    process::Stdio,
};

use ray_core::pathlib::RayPaths;

pub(crate) fn run_backend<C: AsRef<OsStr>>(
    ray_paths: RayPaths,
    subcmd: C,
    argv: Vec<OsString>,
) -> () {
    let bin_path = ray_paths.get_backend_path();
    let lib_path = ray_paths.get_root() / "lib";
    let mut cmd = std::process::Command::new(bin_path.to_string());
    cmd.arg(subcmd).args(argv);

    if lib_path.exists() {
        let llvm_lib_os = lib_path.as_ref();
        #[cfg(target_os = "macos")]
        {
            let value = prepend_env_path("DYLD_LIBRARY_PATH", llvm_lib_os);
            cmd.env("DYLD_LIBRARY_PATH", value);
        }
        #[cfg(target_os = "linux")]
        {
            let value = prepend_env_path("LD_LIBRARY_PATH", llvm_lib_os);
            cmd.env("LD_LIBRARY_PATH", value);
        }
    }

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

fn prepend_env_path(var: &str, new_path: &Path) -> OsString {
    let mut value = OsString::from(new_path.as_os_str());
    if let Some(existing) = env::var_os(var) {
        if !existing.is_empty() {
            value.push(OsStr::new(":"));
            value.push(existing);
        }
    }
    value
}
