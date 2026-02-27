/// Writes `val` as a decimal string into `buf` (which must be at least 12 bytes).
/// Returns a pointer to the start of the written digits within `buf`.
/// The caller can compute the length as `buf + buf_len - returned_ptr`.
#[no_mangle]
pub unsafe extern "C" fn __wasi_itoa(val: u32, buf: *mut u8, buf_len: u32) -> *mut u8 {
    let mut v = val;
    let mut idx = buf_len as usize;

    loop {
        idx -= 1;
        *buf.add(idx) = b'0' + (v % 10) as u8;
        v /= 10;
        if v == 0 {
            break;
        }
    }

    buf.add(idx)
}
