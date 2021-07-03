use std::{
    alloc::{GlobalAlloc, Layout},
    mem,
};

static WEE: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[no_mangle]
pub unsafe extern "C" fn __wasi_malloc(size: usize) -> *mut u8 {
    let layout = Layout::from_size_align(size, mem::size_of::<u8>()).unwrap();
    WEE.alloc(layout)
}
