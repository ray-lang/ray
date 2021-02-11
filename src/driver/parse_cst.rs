use structopt::StructOpt;

use crate::pathlib::FilePath;

#[derive(Debug, StructOpt)]
pub struct CSTOptions {
    #[structopt(name = "INPUT", help = "entrypoint of the program")]
    pub input_path: FilePath,
}
