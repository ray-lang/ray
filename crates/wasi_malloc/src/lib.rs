#![no_std]
#![cfg(target_arch = "wasm32")]

use core::ptr;

const ALIGN: usize = 8;
const PAGE_SIZE: usize = 65536;

/// Block header stored immediately before each allocation.
/// For free blocks, `next` points to the next free block.
/// For allocated blocks, `next` is unused.
struct BlockHeader {
    size: usize,
    next: *mut BlockHeader,
}

const HEADER_SIZE: usize = core::mem::size_of::<BlockHeader>();

/// Global allocator state.
static mut FREE_LIST: *mut BlockHeader = ptr::null_mut();
static mut HEAP_END: usize = 0;

/// Align `val` up to the nearest multiple of `align`.
#[inline(always)]
fn align_up(val: usize, align: usize) -> usize {
    (val + align - 1) & !(align - 1)
}

/// Grow the wasm linear memory to ensure at least `needed` bytes are available
/// starting from `HEAP_END`.
unsafe fn grow_heap(needed: usize) -> *mut u8 {
    let current_pages = core::arch::wasm32::memory_size(0);
    let current_end = current_pages * PAGE_SIZE;

    if HEAP_END == 0 {
        HEAP_END = current_end;
    }

    let alloc_start = align_up(HEAP_END, ALIGN);
    let alloc_end = alloc_start + needed;

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
pub unsafe extern "C" fn __wasi_malloc(size: usize) -> *mut u8 {
    if size == 0 {
        return ptr::null_mut();
    }

    let aligned_size = align_up(size, ALIGN);
    let total = HEADER_SIZE + aligned_size;

    // Search the free list for a block that fits (first-fit).
    let mut prev: *mut BlockHeader = ptr::null_mut();
    let mut curr = FREE_LIST;

    while !curr.is_null() {
        let block_size = (*curr).size;

        if block_size >= aligned_size {
            // Found a fit. Check if we can split.
            let remainder = block_size - aligned_size;
            if remainder >= HEADER_SIZE + ALIGN {
                // Split: create a new free block after the allocated portion.
                let new_block =
                    (curr as *mut u8).add(HEADER_SIZE + aligned_size) as *mut BlockHeader;
                (*new_block).size = remainder - HEADER_SIZE;
                (*new_block).next = (*curr).next;
                (*curr).size = aligned_size;

                // Replace curr with new_block in the free list.
                if prev.is_null() {
                    FREE_LIST = new_block;
                } else {
                    (*prev).next = new_block;
                }
            } else {
                // Use the whole block.
                if prev.is_null() {
                    FREE_LIST = (*curr).next;
                } else {
                    (*prev).next = (*curr).next;
                }
            }

            (*curr).next = ptr::null_mut();
            return (curr as *mut u8).add(HEADER_SIZE);
        }

        prev = curr;
        curr = (*curr).next;
    }

    // No free block found; grow the heap.
    let ptr = grow_heap(total);
    if ptr.is_null() {
        return ptr::null_mut();
    }

    let header = ptr as *mut BlockHeader;
    (*header).size = aligned_size;
    (*header).next = ptr::null_mut();
    ptr.add(HEADER_SIZE)
}

#[no_mangle]
pub unsafe extern "C" fn __wasi_free(ptr: *mut u8) {
    if ptr.is_null() {
        return;
    }

    let header = ptr.sub(HEADER_SIZE) as *mut BlockHeader;

    // Insert into the free list sorted by address for coalescing.
    let mut prev: *mut BlockHeader = ptr::null_mut();
    let mut curr = FREE_LIST;

    while !curr.is_null() && (curr as usize) < (header as usize) {
        prev = curr;
        curr = (*curr).next;
    }

    // Try to coalesce with the next block.
    let header_end = (header as *mut u8).add(HEADER_SIZE + (*header).size);
    if header_end as usize == curr as usize {
        (*header).size += HEADER_SIZE + (*curr).size;
        (*header).next = (*curr).next;
    } else {
        (*header).next = curr;
    }

    // Try to coalesce with the previous block.
    if !prev.is_null() {
        let prev_end = (prev as *mut u8).add(HEADER_SIZE + (*prev).size);
        if prev_end as usize == header as usize {
            (*prev).size += HEADER_SIZE + (*header).size;
            (*prev).next = (*header).next;
        } else {
            (*prev).next = header;
        }
    } else {
        FREE_LIST = header;
    }
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
