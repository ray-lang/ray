use crate::span::Source;

use colored::*;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::{fmt, num::ParseIntError};

pub type RayResult<T = ()> = Result<T, RayError>;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum RayErrorKind {
    Parse,
    Name,
    Import,
    Compile,
    Type,
    IO,
    Unknown,
}

impl fmt::Display for RayErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                RayErrorKind::Parse => "parse error",
                RayErrorKind::Name => "name error",
                RayErrorKind::Import => "import error",
                RayErrorKind::Compile => "compile error",
                RayErrorKind::Type => "type error",
                RayErrorKind::IO => "i/o error",
                RayErrorKind::Unknown => "unknown error",
            }
        )
    }
}

#[derive(Debug)]
pub struct RayError {
    pub msg: String,
    pub src: Vec<Source>,
    pub kind: RayErrorKind,
}

const ELLIPSIS: &'static str = "...";

impl RayError {
    pub fn emit(self) {
        let kind = format!("{}:", self.kind);
        let mut msg_lines = self.msg.lines().collect::<Vec<_>>();
        msg_lines.sort();
        msg_lines.dedup();
        let msg = if msg_lines.len() == 1 {
            msg_lines.pop().unwrap().to_string()
        } else {
            let indent = " ".repeat(kind.len() + 1);
            msg_lines
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    if i == 0 {
                        s.to_string()
                    } else {
                        format!("{}{}", indent, s)
                    }
                })
                .collect::<Vec<_>>()
                .join("\n")
        };

        eprintln!("{} {}", kind.bold().red(), msg.bold());

        // TODO: group sources by filepath
        for src in self.src {
            let arrow = "-->".bold();
            if let Some(span) = src.span {
                let start_line = span.start.lineno;
                let end_line = span.end.lineno;
                let line_count = span.lines();
                let mut f = File::open(&src.filepath).unwrap();
                let mut buf = String::new();
                f.read_to_string(&mut buf).unwrap();

                let max_num_width = if line_count == 1 {
                    (end_line + 1).to_string().len() + 1
                } else {
                    ELLIPSIS.len() + 1
                };
                let full_spacing = " ".repeat(max_num_width);
                let pipe = "|".bold();

                eprintln!(
                    "{}{} {}:{}",
                    " ".repeat(max_num_width - 1),
                    arrow,
                    src.filepath,
                    span
                );
                eprintln!("{}{}", full_spacing, pipe);

                // skip to the start line
                let mut lines = buf.lines().skip(start_line).take(line_count);
                let mut lineno = start_line + 1;
                let red_slash = "/".bold().red();
                let red_pipe = "|".bold().red();
                if line_count == 1 {
                    let line = lines.next().unwrap();
                    let lineno_str = lineno.to_string();
                    let num_width = lineno_str.len();
                    let spacing = " ".repeat(max_num_width - num_width);
                    eprintln!("{}{}{} {}", lineno_str.bold(), spacing, pipe, line);
                    let indent = " ".repeat(span.start.col);
                    let indicator = "^".repeat(span.len()).bold().red();
                    eprintln!("{}{} {}{}", full_spacing, pipe, indent, indicator);
                } else {
                    for (i, line) in lines.enumerate() {
                        lineno += 1;
                        if line_count > 3 && i > 1 && i < line_count - 2 {
                            if i == 2 {
                                let after = line.trim_start();
                                let indent_len = line.len() - after.len();
                                let spacing = " ".repeat(indent_len);
                                eprintln!(
                                    "{} {} {} {}{}",
                                    ELLIPSIS.bold(),
                                    pipe,
                                    red_pipe,
                                    spacing,
                                    ELLIPSIS
                                );
                            }
                            continue;
                        }

                        let lineno_str = lineno.to_string();
                        let num_width = lineno_str.len();
                        let spacing = " ".repeat(max_num_width - num_width);
                        let prefix = if i == 0 { &red_slash } else { &red_pipe };
                        eprintln!(
                            "{}{}{} {} {}",
                            lineno_str.bold(),
                            spacing,
                            pipe,
                            prefix,
                            line
                        );
                    }
                    let indent = "_".repeat(span.end.col + 1).bold().red();
                    let indicator = "^".bold().red();
                    eprintln!(
                        "{}{} {}{}{}",
                        full_spacing, pipe, red_pipe, indent, indicator
                    );
                }
            } else {
                eprintln!(" {} {}", arrow, src.filepath);
            }
        }
        eprintln!()
    }
}

impl From<RayError> for Vec<RayError> {
    fn from(err: RayError) -> Vec<RayError> {
        vec![err]
    }
}

impl From<io::Error> for RayError {
    fn from(err: io::Error) -> RayError {
        RayError {
            msg: err.to_string(),
            src: vec![],
            kind: RayErrorKind::IO,
        }
    }
}

impl From<ParseIntError> for RayError {
    fn from(err: ParseIntError) -> Self {
        // todo
        RayError {
            msg: err.to_string(),
            src: vec![],
            kind: RayErrorKind::Compile,
        }
    }
}
