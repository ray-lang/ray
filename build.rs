use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;

fn rustc_cmd() -> String {
    env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string())
}

fn cargo_cmd() -> String {
    env::var("CARGO").unwrap_or_else(|_| "cargo".to_string())
}

fn probe_wasi_target() -> Result<String, String> {
    let candidates = [
        "wasm32-wasip1",
        "wasm32-wasip1-threads",
        "wasm32-wasip2",
        // legacy last, for older toolchains
        "wasm32-wasi",
    ];

    for target in candidates {
        let out = Command::new(rustc_cmd())
            .args(&[
                "-",
                "--crate-name",
                "___",
                "--print=file-names",
                "--target",
                target,
                "--crate-type",
                "bin",
                "--print=sysroot",
                "--print=cfg",
                "-Wwarnings",
            ])
            .output();

        match out {
            Ok(o) if o.status.success() => return Ok(target.to_string()),
            _ => {}
        }
    }

    Err("No supported WASI target found. Install wasm32-wasip1 or use an older toolchain that still has wasm32-wasi.".into())
}

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let project_dir = Path::new(&manifest_dir);
    let wasi_target = probe_wasi_target().expect("Failed to find a supported WASI target");

    Command::new(cargo_cmd())
        .args(&[
            "rustc",
            &format!("--target={}", wasi_target),
            "--release",
            "--",
            "-C",
            "link-args=--relocatable",
            "-C",
            "link-args=--no-gc-sections",
            "-o",
        ])
        .arg(project_dir.join("lib/libc/wasi_malloc"))
        .current_dir("./crates/wasi_malloc")
        .status()
        .unwrap();

    // fs::remove_file(project_dir.join("lib/libc/wasi_malloc.wasm")).unwrap();
    fs::remove_file(project_dir.join("lib/libc/wasi_malloc.d")).unwrap();

    println!("cargo:rerun-if-changed=crates/wasi_malloc/src");
    println!("cargo:rerun-if-changed=build.rs");
}
