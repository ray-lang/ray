use crate::driver::{BuildOptions, Driver};
use log;
use std::time::Instant;

pub(super) fn action(driver: &mut Driver, options: BuildOptions) {
    let start_time = Instant::now();
    log::info!("Building for {}", options.get_target());
    match driver.build(options) {
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
