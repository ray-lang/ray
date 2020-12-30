use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::io;
use std::ops::Div;
use std::path::{Path, PathBuf, MAIN_SEPARATOR};
use std::str::FromStr;

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct FilePath {
    buf: PathBuf,
}

impl FilePath {
    pub fn new() -> FilePath {
        FilePath {
            buf: PathBuf::new(),
        }
    }

    pub fn sep() -> String {
        String::from(MAIN_SEPARATOR)
    }

    pub fn is_empty(&self) -> bool {
        self.buf.components().count() == 0
    }

    pub fn exists(&self) -> bool {
        self.buf.exists()
    }

    pub fn push<P: AsRef<Path>>(&mut self, path: P) {
        self.buf.push(path);
    }

    /// Returns the final component of the `FilePath`, if there is one.
    ///
    /// If the path is a normal file, this is the file name. If it's the path of a directory, this
    /// is the directory name.
    ///
    /// Returns [`None`] if the path terminates in `..`.
    pub fn file_name(&self) -> String {
        self.buf
            .file_name()
            .expect(&format!("expected a filename but found {}", self))
            .to_str()
            .unwrap()
            .to_string()
    }

    /// Creates an owned [`FilePath`] like `self` but with the given file name.
    pub fn with_file_name<S: AsRef<OsStr>>(&self, file_name: S) -> FilePath {
        FilePath {
            buf: self.buf.with_file_name(file_name),
        }
    }

    pub fn with_extension<S: AsRef<OsStr>>(&self, ext: S) -> FilePath {
        FilePath {
            buf: self.buf.with_extension(ext),
        }
    }

    pub fn has_extension<S: AsRef<OsStr>>(&self, ext: S) -> bool {
        self.buf.extension().map_or(false, |e| e == ext.as_ref())
    }

    /// Extracts the stem (non-extension) portion of [`self.file_name`].
    ///
    /// [`self.file_name`]: FilePath::file_name
    ///
    /// The stem is:
    ///
    /// * [`None`], if there is no file name;
    /// * The entire file name if there is no embedded `.`;
    /// * The entire file name if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name before the final `.`
    pub fn file_stem(&self) -> String {
        self.buf.file_stem().unwrap().to_str().unwrap().to_string()
    }

    /// Returns the filepath of the parent directory
    ///
    /// If the path is already a directory, the path is cloned
    pub fn dir(&self) -> FilePath {
        if self.buf.is_dir() {
            self.clone()
        } else {
            FilePath {
                buf: self.buf.parent().unwrap().to_path_buf(),
            }
        }
    }

    pub fn is_dir(&self) -> bool {
        self.buf.is_dir()
    }

    pub fn read_dir(&self) -> io::Result<fs::ReadDir> {
        self.buf.read_dir()
    }
}

impl fmt::Display for FilePath {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.buf.display())
    }
}

impl<T: Into<PathBuf>> From<T> for FilePath {
    fn from(s: T) -> FilePath {
        FilePath { buf: s.into() }
    }
}

impl FromStr for FilePath {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<FilePath, &'static str> {
        Ok(FilePath { buf: s.into() })
    }
}

impl<T: AsRef<Path>> Div<T> for FilePath {
    type Output = FilePath;

    fn div(self, rhs: T) -> Self::Output {
        FilePath {
            buf: self.buf.join(rhs),
        }
    }
}

impl<T: AsRef<Path>> Div<T> for Box<FilePath> {
    type Output = FilePath;

    fn div(self, rhs: T) -> Self::Output {
        FilePath {
            buf: self.buf.join(rhs),
        }
    }
}

impl<'a, T: AsRef<Path>> Div<T> for &'a FilePath {
    type Output = FilePath;

    fn div(self, rhs: T) -> Self::Output {
        FilePath {
            buf: self.buf.join(rhs),
        }
    }
}

impl AsRef<Path> for FilePath {
    fn as_ref(&self) -> &Path {
        self.buf.as_path()
    }
}
