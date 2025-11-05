use ray_driver::{AnalyzeOptions, Driver};

pub(super) fn action(driver: &mut Driver, options: AnalyzeOptions) {
    let report = driver.analyze(options);
    report.emit();
}
