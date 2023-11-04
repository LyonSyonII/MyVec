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
    /// Pointer to the start of the allocation.
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
    /// Returns a reference to the element at the given index or `None` if the index is out of bounds.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let deque = Deque::from_iter(0..=4);
    /// assert_eq!(deque.get(0), Some(&0));
    /// assert_eq!(deque.get(2), Some(&2));
    /// assert_eq!(deque.get(4), Some(&4));
    /// ```
    pub fn get<I>(&self, index: I) -> Option<&T>
    where
        I: std::slice::SliceIndex<[T], Output = T>,
    {
        self.as_ref().get(index)
    }
    /// Returns a reference to the element at the given index.  
    /// Does not check bounds.
    ///
    /// For a safe alternative see `get`.
    ///
    /// # Safety
    /// * index < self.len()
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let deque = Deque::from_iter(0..=4);
    /// unsafe {
    ///     assert_eq!(deque.get_unchecked(0), &0);
    ///     assert_eq!(deque.get_unchecked(2), &2);
    ///     assert_eq!(deque.get_unchecked(4), &4);
    /// }
    /// ```
    pub unsafe fn get_unchecked<I>(&self, index: I) -> &T
    where
        I: std::slice::SliceIndex<[T], Output = T>,
    {
        self.as_ref().get_unchecked(index)
    }
    /// Returns a mutable reference to the element at the given index or `None` if the index is out of bounds.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::from_iter(0..=4);
    /// if let Some(n) = deque.get_mut(2) {
    ///     *n = 6;
    /// }
    /// assert_eq!(deque, [0, 1, 6, 3, 4]);
    /// ```
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut T>
    where
        I: std::slice::SliceIndex<[T], Output = T>,
    {
        self.as_mut().get_mut(index)
    }
    /// Returns a mutable reference to the element at the given index.  
    /// Does not check bounds.
    ///
    /// For a safe alternative see `get_mut`.
    ///
    /// # Safety
    /// * index < self.len()
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::from_iter(0..=4);
    /// unsafe { *deque.get_unchecked_mut(2) = 6 };
    /// assert_eq!(deque, [0, 1, 6, 3, 4]);
    /// ```
    pub unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut T
    where
        I: std::slice::SliceIndex<[T], Output = T>,
    {
        self.as_mut().get_unchecked_mut(index)
    }
    /// Pushes a new element to the back of the deque.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::new();
    /// assert_eq!(deque.capacity(), 0);
    /// assert_eq!([deque.start(), deque.end()], [0, 0]);
    ///
    /// deque.push_back(10);
    /// assert_eq!(deque.capacity(), 4);
    /// assert_eq!([deque.start(), deque.end()], [0, 1]);
    /// assert_eq!(deque.as_slice(), &[10]);
    ///
    /// deque.push_back(11);
    /// assert_eq!(deque.capacity(), 4);
    /// assert_eq!([deque.start(), deque.end()], [0, 2]);
    /// assert_eq!(deque.as_slice(), &[10, 11]);
    ///
    /// deque.push_back(12);
    /// assert_eq!(deque.capacity(), 8);
    /// assert_eq!([deque.start(), deque.end()], [0, 3]);
    /// assert_eq!(deque.len(), 3);
    /// assert_eq!(deque.as_slice(), &[10, 11, 12]);
    /// ```
    pub fn push_back(&mut self, value: T) {
        self.realloc_if_necessary();
        unsafe { self.endptr().write(value) };
        self.end += 1;
    }
    /// Pushes a new element to the front of the deque.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::new();
    /// deque.push_front(0);
    /// deque.push_front(1);
    /// deque.push_front(2);
    /// assert_eq!(deque, [2, 1, 0]);
    pub fn push_front(&mut self, value: T) {
        self.realloc_if_necessary();
        self.start += 1;
        unsafe { self.startptr().write(value) };
    }
    /// Removes the last element from the deque and returns it.
    ///
    /// If the deque is empty, `None` is returned.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::new();
    /// deque.push_back(0);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// assert_eq!(deque.as_slice(), &[0, 1, 2, 3, 4]);
    /// assert_eq!(deque.pop_back(), Some(4));
    /// assert_eq!(deque.pop_back(), Some(3));
    /// assert_eq!(deque.pop_back(), Some(2));
    /// assert_eq!(deque.pop_back(), Some(1));
    /// assert_eq!(deque.pop_back(), Some(0));
    /// assert_eq!(deque.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.end -= 1;
            Some(unsafe { self.endptr().read() })
        }
    }
    /// Returns the contents of the deque as a slice.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let deque = Deque::from_iter(0..=2);
    /// assert_eq!(deque.as_slice(), &[0, 1, 2]);
    pub fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.startptr(), self.len()) }
    }
    /// Returns the contents of the deque as a mutable slice.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::from_iter([2, 0, 1]);
    /// deque.as_mut_slice().sort();
    /// assert_eq!(deque.as_slice(), &[0, 1, 2]);
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.startptr(), self.len()) }
    }
    /// Returns the currently allocated capacity.
    pub fn capacity(&self) -> usize {
        self.capacity
    }
    /// Returns the currently allocated capacity at the front of the `Deque`.
    ///
    /// If more than `front_capacity()` elements are inserted with `push_front()`, the `Deque` will reallocate.
    pub fn front_capacity(&self) -> usize {
        self.capacity / 2 - self.start
    }
    /// Returns the currently allocated capacity at the back of the `Deque`.
    ///
    /// If more than `back_capacity()` elements are inserted with `push_back()`, the `Deque` will reallocate.
    pub fn back_capacity(&self) -> usize {
        self.capacity / 2 - self.end
    }
    /// Returns the start offset of the deque.
    ///
    /// It's also the number of elements that have been inserted with `push_front()`.
    pub fn start(&self) -> usize {
        self.start
    }
    /// Returns the end offset of the deque.
    ///
    /// It's also the number of elements that have been inserted with `push_back()`.
    pub fn end(&self) -> usize {
        self.end
    }
    /// Reserves capacity for at least `additional` more elements to be inserted in the `Deque`, either at the front or the back.
    ///
    /// If you know if the new items will be inserted at the front or back, you can use `reserve_front()` or `reserve_back()`.
    ///
    /// New capacity will be the next power of two large enough to hold the additional elements.
    ///
    /// If `T` is a ZST, the `Deque`'s capacity is always 0, so this will do nothing.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::<u8>::new();
    /// deque.reserve(6);
    /// assert_eq!(deque.capacity(), 16);
    ///
    /// // `deque` still has len == 0, so up to 8 elements can be inserted without reallocating
    /// deque.reserve(3);
    /// assert_eq!(deque.capacity(), 16);
    ///
    /// // If we `push_back` 8 elements and reserve for 1, the capacity will double as expected
    /// deque.extend(0..8);
    /// assert_eq!(deque.capacity(), 16);
    /// assert_eq!(deque.back_capacity(), 0);
    /// deque.reserve(1);
    /// assert_eq!(deque.capacity(), 32);
    /// assert_eq!(deque.back_capacity(), 8);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        if self.front_capacity() >= additional && self.back_capacity() >= additional {
            return;
        }
        let new_capacity = (self.len() + additional) * 2;
        self.realloc_with_capacity(new_capacity.next_power_of_two())
    }
    /// Reserves capacity for at least `additional` more elements to be inserted at the back of the `Deque`.
    ///
    /// New capacity will be the next power of two large enough to hold the additional elements.
    ///
    /// If `T` is a ZST, the `Deque`'s capacity is always 0, so this will do nothing.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::<u8>::new();
    /// deque.reserve_back(6);
    /// assert_eq!(deque.capacity(), 16);
    ///
    /// // `deque` still has len == 0, so up to 8 elements can be inserted without reallocating
    /// deque.reserve_back(3);
    /// assert_eq!(deque.capacity(), 16);
    ///
    /// // If we `push_back` 8 elements and reserve for 1, the capacity will double as expected
    /// deque.extend(0..8);
    /// assert_eq!(deque.capacity(), 16);
    /// assert_eq!(deque.back_capacity(), 0);
    /// deque.reserve_back(1);
    /// assert_eq!(deque.capacity(), 32);
    /// assert_eq!(deque.back_capacity(), 8);
    /// ```
    pub fn reserve_back(&mut self, additional: usize) {
        if self.back_capacity() >= additional {
            return;
        }
        let new_capacity = (self.len() + additional) * 2;
        self.realloc_with_capacity(new_capacity.next_power_of_two())
    }
    /// Reserves capacity for at least `additional` more elements to be inserted at the front of the `Deque`.
    ///
    /// New capacity will be the next power of two large enough to hold the additional elements.
    ///
    /// If `T` is a ZST, the `Deque`'s capacity is always 0, so this will do nothing.
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let mut deque = Deque::<u8>::new();
    /// deque.reserve_front(6);
    /// assert_eq!(deque.capacity(), 16);
    ///
    /// // `deque` still has len == 0, so up to 8 elements can be inserted without reallocating
    /// deque.reserve_front(3);
    /// assert_eq!(deque.capacity(), 16);
    ///
    /// // If we `push_back` 8 elements and reserve_front for 1, the capacity will stay the same
    /// deque.extend(0..8);
    /// assert_eq!(deque.capacity(), 16);
    /// assert_eq!(deque.front_capacity(), 8);
    /// deque.reserve_front(1);
    /// assert_eq!(deque.capacity(), 16);
    /// assert_eq!(deque.front_capacity(), 8);
    /// ```
    pub fn reserve_front(&mut self, additional: usize) {
        if self.front_capacity() >= additional {
            return;
        }
        let new_capacity = (self.len() + additional) * 2;
        self.realloc_with_capacity(new_capacity.next_power_of_two())
    }
    /// An iterator over references to the elements of a [`Deque`].
    ///
    /// # Example
    /// ```
    /// use mycollections::Deque;
    ///
    /// let deque = Deque::from_iter(0..=4);
    /// let mut iter = deque.iter();
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&3));
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }
    fn realloc_if_necessary(&mut self) {
        if self.start >= self.capacity / 2 || self.end >= self.capacity / 2 {
            self.realloc_with_capacity(4.max(self.capacity * 2))
        }
    }
    /// ```bash
    /// # Before reallocation
    /// [x,  x,  0,  1]
    ///          |    |
    ///        start end
    /// # Without copy_nonoverlapping (grows to the right)
    /// [x,  x,  0,  1,  x,  x,  x,  x]
    ///                  |       |
    ///                start    end
    /// # With copy_nonoverlapping (grows both sides equally)
    /// [x, x, x, x, 0, 1, x, x]
    ///              |     |
    ///            start  end
    fn realloc_with_capacity(&mut self, new_capacity: usize) {
        let Some(new_ptr) = crate::alloc_array::<T>(new_capacity) else {
            return;
        };

        // `src` is the start of deque
        let src = self.startptr();
        // `dst` = middle of new deque - start
        let dst = unsafe { new_ptr.as_ptr().add(new_capacity / 2 - self.start) };
        // copy valid elements from old deque to new
        unsafe { std::ptr::copy_nonoverlapping(src, dst, self.len()) };
        crate::dealloc_array(self.ptr, self.capacity);
        self.ptr = new_ptr;
        self.capacity = new_capacity;
    }
    fn middleptr(&self) -> *mut T {
        unsafe { self.ptr.as_ptr().add(self.capacity / 2) }
    }
    /// Returns a pointer to the start of the deque.
    ///
    /// The pointer can be read as long as the deque is not empty.
    fn startptr(&self) -> *mut T {
        unsafe { self.middleptr().sub(self.start) }
    }
    /// Returns a pointer to the end of the deque.
    ///
    /// The pointer cannot be read, as it represents the end boundary of the deque.
    ///
    /// If you want to access the last element, use `endptr().as_ptr().sub(1)`
    /// ```bash
    ///    [0, 1, 2, 3]
    ///    |          |
    ///  start       end
    /// ```
    fn endptr(&self) -> *mut T {
        unsafe { self.middleptr().add(self.end) }
    }
}

impl<T> Drop for Deque<T> {
    fn drop(&mut self) {
        crate::dealloc_array(self.ptr, self.capacity)
    }
}

impl<T> FromIterator<T> for Deque<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut deque = Deque::new();
        deque.extend(iter);
        deque
    }
}

impl<T> Extend<T> for Deque<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        if let (_, Some(len)) = iter.size_hint() {
            self.reserve_back(len);
        }
        for item in iter {
            self.push_back(item);
        }
    }
}

impl<T> AsRef<[T]> for Deque<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsMut<[T]> for Deque<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, Slice> PartialEq<Slice> for Deque<T>
where
    T: PartialEq,
    Slice: AsRef<[T]>,
{
    fn eq(&self, other: &Slice) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T> core::fmt::Debug for Deque<T>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

/// An iterator over references to the elements of a [`Deque`].
///
/// # Example
/// ```
/// use mycollections::Deque;
///
/// let deque = Deque::from_iter(0..=4);
/// let mut iter = deque.iter();
/// assert_eq!(iter.next(), Some(&0));
/// assert_eq!(iter.next(), Some(&1));
/// assert_eq!(iter.next(), Some(&2));
/// assert_eq!(iter.next(), Some(&3));
/// assert_eq!(iter.next(), Some(&4));
/// assert_eq!(iter.next(), None);
/// ```
pub struct Iter<'a, T> {
    deque: &'a Deque<T>,
    index: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.index += 1;
        self.deque.get(self.index - 1)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.deque.len() - self.index;
        (len, Some(len))
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<'a, T> IntoIterator for &'a Deque<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            deque: self,
            index: 0,
        }
    }
}
