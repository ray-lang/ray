#![no_std]
#![cfg(target_arch = "wasm32")]

use core::ptr;

const PAGE_SIZE: usize = 65536;

/// Number of size classes: 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096.
const NUM_CLASSES: usize = 10;

/// Minimum size class exponent (2^3 = 8).
const MIN_CLASS_LOG2: usize = 3;

/// Maximum size handled by the segregated free lists (2^12 = 4096).
const MAX_CLASS_SIZE: usize = 1 << (MIN_CLASS_LOG2 + NUM_CLASSES - 1);

/// One free-list head per size class.
static mut FREE_LISTS: [*mut u8; NUM_CLASSES] = [ptr::null_mut(); NUM_CLASSES];

/// Current end of the heap (bumped on fresh allocations).
static mut HEAP_END: usize = 0;

/// Map a byte size to a size class index. Returns `NUM_CLASSES` for oversized.
#[inline(always)]
fn class_index(size: usize) -> usize {
    if size > MAX_CLASS_SIZE {
        return NUM_CLASSES;
    }
    let size = size.max(1 << MIN_CLASS_LOG2);
    let log2 = usize::BITS as usize - (size - 1).leading_zeros() as usize;
    log2.saturating_sub(MIN_CLASS_LOG2)
}

/// Byte size of a given class index.
#[inline(always)]
fn class_size(index: usize) -> usize {
    1 << (index + MIN_CLASS_LOG2)
}

/// Bump the heap pointer, growing wasm memory if needed.
unsafe fn bump_alloc(size: usize, align: usize) -> *mut u8 {
    let current_pages = core::arch::wasm32::memory_size(0);
    let current_end = current_pages * PAGE_SIZE;

    if HEAP_END == 0 {
        HEAP_END = current_end;
    }

    let alloc_start = (HEAP_END + align - 1) & !(align - 1);
    let alloc_end = alloc_start + size;

    if alloc_end > current_end {
        let pages_needed = (alloc_end - current_end + PAGE_SIZE - 1) / PAGE_SIZE;
        let result = core::arch::wasm32::memory_grow(0, pages_needed);
        if result == usize::MAX {
            return ptr::null_mut();
        }
    }

    HEAP_END = alloc_end;
    alloc_start as *mut u8
}

#[no_mangle]
pub unsafe extern "C" fn __wasi_alloc(size: usize, align: usize) -> *mut u8 {
    if size == 0 {
        return ptr::null_mut();
    }

    // Effective size: at least `align` (for alignment), rounded up to a power of 2.
    let effective = size.max(align).next_power_of_two().max(1 << MIN_CLASS_LOG2);
    let idx = class_index(effective);

    if idx < NUM_CLASSES {
        // Try the free list for this size class.
        let head = FREE_LISTS[idx];
        if !head.is_null() {
            // Pop: read the `next` pointer stored in the block body.
            FREE_LISTS[idx] = *(head as *const *mut u8);
            return head;
        }
        // No free block — bump-allocate a new one at the class size.
        return bump_alloc(class_size(idx), effective);
    }

    // Oversized: bump-allocate directly.
    bump_alloc(effective, align)
}

#[no_mangle]
pub unsafe extern "C" fn __wasi_dealloc(ptr: *mut u8, size: usize, align: usize) {
    if ptr.is_null() {
        return;
    }

    let effective = size.max(align).next_power_of_two().max(1 << MIN_CLASS_LOG2);
    let idx = class_index(effective);

    if idx < NUM_CLASSES {
        // Push: store the current head as `next` in the freed block, then update head.
        *(ptr as *mut *mut u8) = FREE_LISTS[idx];
        FREE_LISTS[idx] = ptr;
    }
    // Oversized blocks are leaked (not returned to a free list).
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
