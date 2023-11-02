//! My implementation of Rust's [`VecDeque`](std::collections::VecDeque).
//!
//! Implemented methods should behave exactly like the original.
//!
//! It is NOT implemented as a Ring Buffer, instead it uses half of the capacity as the start and
//! half as the end.
//!
//! This ensures that memory is always contiguous.

/// My implementation of Rust's [`Vec`](std::vec::Vec).
///
/// Implemented methods should behave exactly like the original.
pub struct Deque<T> {
    /// Negative offset from `ptr` to the start of the deque.
    start: usize,
    /// Positive offset from `ptr` to the end of the deque.
    end: usize,
    /// Currently allocated capacity.
    capacity: usize,
    /// Pointer to the middle of the allocation.
    ptr: core::ptr::NonNull<T>,
    _marker: core::marker::PhantomData<T>,
}

impl<T> Deque<T> {
    /// Creates a new `Deque`, does not allocate.
    pub const fn new() -> Deque<T> {
        Deque {
            start: 0,
            end: 0,
            capacity: 0,
            ptr: core::ptr::NonNull::dangling(),
            _marker: core::marker::PhantomData,
        }
    }
    /// Returns the length of the deque.
    pub const fn len(&self) -> usize {
        self.start + self.end
    }
    /// Returns `true` if the deque is empty.
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn realloc_if_necessary(&mut self) {
        if self.start == self.capacity / 2 || self.end == self.capacity / 2 {
            self.realloc_with_capacity(2.max(self.capacity * 2))
        }
    }
    fn realloc_with_capacity(&mut self, new_capacity: usize) {
        if let Some(ptr) = crate::realloc_array(self.ptr, self.capacity, new_capacity) {
            self.ptr = ptr;
            self.capacity = new_capacity;
        }
    }
    /// Returns the `Layout` of the current allocation.
    const fn layout(&self) -> core::alloc::Layout {
        let size = core::mem::size_of::<T>() * self.capacity;
        let align = core::mem::align_of::<T>();
        unsafe { core::alloc::Layout::from_size_align_unchecked(size, align) }
    }
}
