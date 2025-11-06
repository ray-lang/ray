use ray_core::pathlib::RayPaths;
use ray_driver::{AnalyzeOptions, GlobalOptions};

use crate::cli::backend::run_backend;

pub(super) fn action(ray_paths: RayPaths, options: AnalyzeOptions, globals: GlobalOptions) {
    let argv = options.to_argv(globals);
    run_backend(ray_paths, "analyze", argv);
}
