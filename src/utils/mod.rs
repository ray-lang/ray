pub fn indent(s: String, n: usize) -> String {
    let mut dst = String::new();
    for (i, line) in s.lines().enumerate() {
        if i != 0 {
            dst.push('\n');
        }
        if line.len() != 0 {
            dst.push_str(&"  ".repeat(n));
            dst.push_str(line);
        }
    }
    dst
}

pub fn join<'a, T, S>(i: T, sep: S) -> String
where
    T: IntoIterator,
    T::Item: ToString,
    S: Into<&'a str>,
{
    i.into_iter()
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(sep.into())
}

pub fn map_join<'a, T, S, F>(i: T, sep: S, f: F) -> String
where
    T: IntoIterator,
    S: Into<&'a str>,
    F: Fn(T::Item) -> String,
{
    i.into_iter().map(f).collect::<Vec<_>>().join(sep.into())
}

pub fn replace<F, T>(dest: &mut T, f: F)
where
    F: FnOnce(T) -> T,
{
    unsafe {
        let old = std::mem::replace(dest, std::mem::MaybeUninit::uninit().assume_init());
        let src = f(old);
        let uninit = std::mem::replace(dest, src);
        std::mem::forget(uninit);
    }
}

pub fn try_replace<F, T, E>(dest: &mut T, f: F) -> Result<(), E>
where
    F: FnOnce(T) -> Result<T, E>,
{
    unsafe {
        let old = std::mem::replace(dest, std::mem::MaybeUninit::uninit().assume_init());
        let src = f(old)?;
        let uninit = std::mem::replace(dest, src);
        std::mem::forget(uninit);
        Ok(())
    }
}

// pub fn replace_result<F, T>(dest: &mut T, f: F)
// where
//     F: FnOnce(T) -> (T, U),
// {
//     let old = unsafe {
//         std::mem::replace(dest, std::mem::MaybeUninit::uninit().assume_init())
//     };

//     let src = f(old);
//     let uninit = std::mem::replace(dest, src);
//     std::mem::forget(uninit);

// }
