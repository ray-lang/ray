use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let project_dir = Path::new(&manifest_dir);

    Command::new("cargo")
        .args(&[
            "rustc",
            "--target=wasm32-wasi",
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
