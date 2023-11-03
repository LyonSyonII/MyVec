#![deny(missing_docs)]

//! My own implementations of the data structures in the Rust `std::collections` module.
//!
//! All methods and structs are fully documented (enforced by `#[deny(missing_docs)]`).
//!
//! All collections support ZSTs (zero-sized types).
//!
//! Currently implemented:
//! - `Vec`
//! - `LinkedList`

pub mod deque;
pub mod linked_list;
pub mod vec;

pub use deque::Deque;
pub use linked_list::LinkedList;
pub use vec::Vec;

/// Allocates enough memory for [T; size].
///
/// Returns `None` if `T` is a ZST (zero-sized type) or if `size == 0`.
pub(crate) fn alloc_array<T>(size: usize) -> Option<core::ptr::NonNull<T>> {
    let layout = array_layout::<T>(size);
    if layout.size() == 0 {
        return None;
    }
    let alloc = unsafe { std::alloc::alloc(layout) };
    if alloc.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    unsafe { Some(core::ptr::NonNull::new_unchecked(alloc as *mut T)) }
}
/// Reallocates memory from `[old_ptr; old_layout]` to `[T; new_size]`.
///
/// If `old_size == 0`, allocates memory for [T; new_size] without reallocating.
///
/// Returns `None` if `T` is a ZST (zero-sized type) or if `size == 0`.
pub(crate) fn realloc_array<T>(
    old_ptr: core::ptr::NonNull<T>,
    old_size: usize,
    new_size: usize,
) -> Option<core::ptr::NonNull<T>> {
    let new_layout = array_layout::<T>(new_size);
    if new_layout.size() == 0 {
        return None;
    }
    // SAFETY:
    let alloc = if old_size == 0 {
        unsafe { std::alloc::alloc(new_layout) }
    } else {
        let old_ptr = old_ptr.as_ptr() as *mut u8;
        let old_layout = array_layout::<T>(old_size);
        unsafe { std::alloc::realloc(old_ptr, old_layout, new_layout.size()) }
    };
    if alloc.is_null() {
        std::alloc::handle_alloc_error(new_layout);
    }
    // SAFETY: Size and alignment are correct, pointer is not null
    unsafe { Some(core::ptr::NonNull::new_unchecked(alloc as *mut T)) }
}

/// Deallocates memory for a `[T; size]`.
/// 
/// If `size == 0`, does nothing.
pub(crate) fn dealloc_array<T>(ptr: core::ptr::NonNull<T>, size: usize) {
    let layout = array_layout::<T>(size);
    if layout.size() == 0 {
        return;
    }
    // SAFETY: Size and alignment are correct, size > 0
    unsafe { std::alloc::dealloc(ptr.as_ptr().cast(), layout)}
}

pub(crate) const fn array_layout<T>(size: usize) -> core::alloc::Layout {
    // SAFETY: The size and alignment are correct.
    unsafe {
        core::alloc::Layout::from_size_align_unchecked(
            core::mem::size_of::<T>() * size,
            core::mem::align_of::<T>(),
        )
    }
}
