use std::ffi::CStr;
use std::{
    ffi::CString,
    os::raw::{c_char, c_int},
};

#[repr(C)]
struct LLDInvokeResult {
    success: bool,
    messages: *const c_char,
}

extern "C" {
    fn lld_link(flavor: *const c_char, argc: c_int, argv: *const *const c_char) -> LLDInvokeResult;
    fn link_free_result(result: *mut LLDInvokeResult);
}

pub enum LLDError {
    StringConversionError,
}

pub struct LLDResult {
    success: bool,
    messages: String,
}

impl LLDResult {
    pub fn ok(self) -> Result<(), String> {
        if self.success {
            Ok(())
        } else {
            Err(self.messages)
        }
    }
}

/// Invokes LLD of the given flavor with the specified arguments.
pub fn link(flavor: String, args: &[String]) -> LLDResult {
    // Prepare arguments
    let c_args = args
        .iter()
        .map(|arg| CString::new(arg.as_bytes()).unwrap())
        .collect::<Vec<CString>>();
    let args: Vec<*const c_char> = c_args.iter().map(|arg| arg.as_ptr()).collect();

    // Invoke LLD
    let flavor = CString::new(flavor.as_bytes()).unwrap();
    let mut lld_result = unsafe { lld_link(flavor.as_ptr(), args.len() as c_int, args.as_ptr()) };

    // Get the messages from the invocation
    let messages = if !lld_result.messages.is_null() {
        unsafe {
            CStr::from_ptr(lld_result.messages)
                .to_string_lossy()
                .to_string()
        }
    } else {
        String::new()
    };

    // Construct the result
    let result = LLDResult {
        success: lld_result.success,
        messages,
    };

    // Release the result
    unsafe { link_free_result(&mut lld_result as *mut LLDInvokeResult) };
    drop(lld_result);

    result
}
