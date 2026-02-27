fn main() {
    let fingerprint = std::env::var("RAY_BUILD_FINGERPRINT").unwrap_or_else(|_| "dev".to_string());

    let out_dir = std::env::var("OUT_DIR").unwrap();
    let path = std::path::Path::new(&out_dir).join("fingerprint.rs");
    std::fs::write(
        path,
        format!("pub const BUILD_FINGERPRINT: &str = \"{}\";\n", fingerprint),
    )
    .unwrap();

    println!("cargo:rerun-if-env-changed=RAY_BUILD_FINGERPRINT");
}
