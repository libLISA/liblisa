use core::{mem::MaybeUninit, alloc::{GlobalAlloc, Layout}, ptr::null_mut};
use linked_list_allocator::LockedHeap;

#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

pub fn init(heap: &'static mut [MaybeUninit<u8>]) {
    ALLOCATOR.lock().init_from_slice(heap)
}

pub struct Dummy;

unsafe impl GlobalAlloc for Dummy {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        null_mut()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        panic!("dealloc should be never called")
    }
}