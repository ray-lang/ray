use colored::{Color, ColoredString, Colorize};
use log::Level;

pub fn base(level: log::LevelFilter) -> fern::Dispatch {
    fern::Dispatch::new().level(level)
}

pub fn default(level: log::LevelFilter) -> fern::Dispatch {
    base(level)
}

pub fn stderr(base: fern::Dispatch) -> fern::Dispatch {
    base.format(move |out, message, record| {
        let level = record.level();
        let color = match level {
            Level::Error => Color::Red,
            Level::Warn => Color::Yellow,
            Level::Info => Color::Blue,
            Level::Debug => Color::Magenta,
            Level::Trace => Color::Green,
        };
        out.finish(format_args!(
            "{} {}",
            ColoredString::from((level.to_string().to_lowercase() + ":").as_str())
                .color(color)
                .to_string(),
            message
        ))
    })
    .chain(std::io::stderr())
}

pub fn init(level: log::LevelFilter) -> () {
    stderr(default(level)).apply().unwrap();
}
