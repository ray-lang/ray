#![no_std]
#![cfg(target_arch = "wasm32")]

mod alloc;
mod itoa;
mod strlen;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
