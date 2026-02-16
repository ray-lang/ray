use std::process;

use ray_shared::pathlib::FilePath;
use wasmtime::{Engine, Linker, Module, Store};
use wasmtime_wasi::p1::WasiP1Ctx;
use wasmtime_wasi::{I32Exit, WasiCtxBuilder};

use ray_driver::{BuildOptions, Driver, TestOptions};

pub(super) fn action(driver: &mut Driver, options: TestOptions) {
    // Convert TestOptions into BuildOptions with test_mode enabled
    let build_options = BuildOptions {
        input_path: options.input_path,
        no_core: options.no_core,
        test_mode: true,
        ..Default::default()
    };

    // Build the test binary
    let wasm_path = match driver.build(build_options) {
        Ok(Some(path)) => path,
        Ok(None) => {
            eprintln!("error: build produced no output");
            process::exit(1);
        }
        Err(errs) => {
            driver.emit_errors(errs);
            log::error!("{} errors emitted", driver.errors_emitted);
            process::exit(1);
        }
    };

    // Run the compiled test binary with wasmtime
    // The test harness (_start) prints results and calls proc_exit(1) on failure
    run_wasm(&wasm_path);
}

fn run_wasm(path: &FilePath) {
    let engine = Engine::default();
    let mut linker: Linker<WasiP1Ctx> = Linker::new(&engine);
    wasmtime_wasi::p1::add_to_linker_sync(&mut linker, |t| t)
        .expect("failed to add WASI to linker");

    let wasi_ctx = WasiCtxBuilder::new().inherit_stdio().build_p1();
    let mut store = Store::new(&engine, wasi_ctx);

    let module = Module::from_file(&engine, path).unwrap_or_else(|e| {
        eprintln!("error: failed to load wasm module '{}': {}", path, e);
        process::exit(1);
    });

    let instance = linker.instantiate(&mut store, &module).unwrap_or_else(|e| {
        eprintln!("error: failed to instantiate module: {}", e);
        process::exit(1);
    });

    let start = instance
        .get_typed_func::<(), ()>(&mut store, "_start")
        .unwrap_or_else(|e| {
            eprintln!("error: no _start export: {}", e);
            process::exit(1);
        });

    if let Err(e) = start.call(&mut store, ()) {
        if let Some(exit) = e.downcast_ref::<I32Exit>() {
            process::exit(exit.0);
        }
        eprintln!("error: test execution failed: {}", e);
        process::exit(1);
    }
}
