use crate::driver::{CSTOptions, Driver};
use log;
use std::time::Instant;

pub(super) fn action(driver: &mut Driver, options: CSTOptions) {
    let start_time = Instant::now();
    log::info!("Parsing file into CST...");
    match driver.cst(options) {
        Err(errs) => {
            driver.emit_errors(errs);
            log::error!("{} errors emitted", driver.errors_emitted);
            return;
        }
        _ => (),
    }

    // TODO: a prettier output
    let elapsed = start_time.elapsed();
    log::info!("Compiled in {:?}", elapsed);
}
