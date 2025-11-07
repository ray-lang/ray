use std::time::Instant;

use ray_driver::{BuildOptions, Driver};

pub(super) fn action(driver: &mut Driver, options: BuildOptions) {
    let start_time = Instant::now();
    log::info!("building for {}", options.get_target());
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
    log::info!("compiled in {:?}", elapsed);
}
