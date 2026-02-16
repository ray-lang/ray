use std::process;

use ray_driver::InspectOptions;
use ray_driver::inspect;

pub fn action(options: InspectOptions) {
    let json = options.json;
    match inspect::inspect(&options) {
        Ok(report) => report.emit(json),
        Err(err) => {
            eprintln!("error: {}", err);
            process::exit(1);
        }
    }
}
