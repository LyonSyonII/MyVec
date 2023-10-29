#![deny(missing_docs)]

//! 

/// My own implementation of `Vec`.
/// 
/// Implemented methods should behave exactly like it.
pub struct MyVec<T> {
    len: usize,
    capacity: usize,
    ptr: core::ptr::NonNull<T>,
}

impl<T> MyVec<T> {
    /// Creates a new `MyVec`
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    ///
    /// let mut vec: MyVec<i32> = MyVec::new();
    /// ```
    pub fn new() -> MyVec<T> {
        MyVec {
            len: 0,
            capacity: 0,
            ptr: std::ptr::NonNull::dangling(),
        }
    }
    /// Reserves capacity for at least `additional` more elements to be inserted in the `MyVec`.
    /// 
    /// New capacity will be the next power of two large enough to hold the additional elements.
    /// 
    /// If `T` is a ZST, the `MyVec`'s capacity is always 0, so this will do nothing.
    /// 
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    /// 
    /// let mut vec = MyVec::<u8>::new();
    /// vec.reserve(6);
    /// assert_eq!(vec.capacity(), 8);
    /// 
    /// // Vec still has len == 0, so 3 elements can be inserted
    /// vec.reserve(3);
    /// assert_eq!(vec.capacity(), 8);
    /// 
    /// // If we insert 8 elements and reserve for 1, the capacity will double as expected
    /// vec.extend(0..8);
    /// assert_eq!(vec.capacity(), 8);
    /// vec.reserve(1);
    /// assert_eq!(vec.capacity(), 16);
    pub fn reserve(&mut self, additional: usize) {
        if self.capacity < self.len + additional {
            let min_capacity = self.len + additional;
            self.realloc_with_capacity(min_capacity.next_power_of_two())
        }
    }
    /// Adds a new element to the `MyVec`
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec[0], 1);
    /// assert_eq!(vec[1], 2);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    pub fn push(&mut self, value: T) {
        self.realloc_if_necessary();
        unsafe {
            self.ptr.as_ptr().add(self.len).write(value);
        }
        self.len += 1;
    }
    /// Inserts a new element at the given index, shifting all elements after it to the right.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    ///
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// vec.push(1);
    /// vec.push(3);
    /// vec.insert(1, 2);
    /// assert_eq!(vec, [1, 2, 3]);
    /// vec.insert(0, 0);
    /// assert_eq!(vec, [0, 1, 2, 3]);
    /// vec.insert(4, 4);
    /// assert_eq!(vec, [0, 1, 2, 3, 4]);
    /// vec.insert(4, 5);
    /// assert_eq!(vec, [0, 1, 2, 3, 5, 4]);
    /// ```
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.len);
        self.realloc_if_necessary();
        let src = unsafe { self.ptr.as_ptr().add(index) };
        let dst = unsafe { src.add(1) };
        unsafe {
            std::ptr::copy(src, dst, self.len - index);
        }
        unsafe {
            src.write(value);
        }
        self.len += 1;
    }
    /// Removes the last element from the `MyVec` and returns it.
    ///
    /// If the `MyVec` is empty, `None` is returned
    ///
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.pop(), Some(2));
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        unsafe { Some(self.ptr.as_ptr().add(self.len).read()) }
    }
    /// Removes the element at the given index and returns it.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    ///
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    ///
    /// let mut vec = MyVec::from_iter(0..5);
    /// assert_eq!(vec.remove(2), 2);
    /// assert_eq!(vec, [0, 1, 3, 4]);
    /// assert_eq!(vec.remove(0), 0);
    /// assert_eq!(vec, [1, 3, 4]);
    /// assert_eq!(vec.remove(2), 4);
    /// assert_eq!(vec, [1, 3]);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len);
        let dst = unsafe { self.ptr.as_ptr().add(index) };
        let src = unsafe { dst.add(1) };
        let ret = unsafe { dst.read() };
        self.len -= 1;
        unsafe {
            std::ptr::copy(src, dst, self.len - index);
        }
        ret
    }
    /// Returns an iterator that removes the elements in `range and yields them.
    /// 
    /// If the iterator is dropped, the remaining elements are removed.
    /// 
    /// # Panics
    /// Panics if the range is out of bounds.
    /// 
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    /// 
    /// let mut vec = MyVec::from_iter(0..=4);
    /// let mut iter = vec.drain(1..=3);
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// 
    /// // Drop the iterator to recover the mutable reference
    /// drop(iter);
    /// assert_eq!(vec, [0, 4]);
    /// 
    /// // Empty ranges return no elements
    /// let mut iter = vec.drain(0..0);
    /// assert_eq!(iter.next(), None);
    /// drop(iter);
    /// 
    /// // Empty ranges will not panic if `end` <= `len`
    /// vec.drain(2..2); 
    /// ```
    pub fn drain(&mut self, range: impl core::ops::RangeBounds<usize>) -> Drain<T>{
        let start = match range.start_bound() {
            core::ops::Bound::Included(&s) => s,
            core::ops::Bound::Excluded(&s) => s + 1,
            core::ops::Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            core::ops::Bound::Included(&e) => e + 1,
            core::ops::Bound::Excluded(&e) => e,
            core::ops::Bound::Unbounded => self.len,
        };
        assert!(start <= end && end <= self.len);
        Drain {
            vec: self,
            start,
            elements: end - start,
        }
    }
    /// Returns the length of the `MyVec`
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.len(), 2);
    /// ```
    pub const fn len(&self) -> usize {
        self.len
    }
    /// Returns `true` if the `MyVec` is empty
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// Returns the capacity of the `MyVec`
    /// # Example
    /// ```
    /// use mycollections::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// assert_eq!(vec.capacity(), 0);
    /// vec.push(1);
    /// assert_eq!(vec.capacity(), 2);
    /// vec.push(2);
    /// assert_eq!(vec.capacity(), 2);
    /// vec.push(3);
    /// assert_eq!(vec.capacity(), 4);
    /// vec.push(4);
    /// assert_eq!(vec.capacity(), 4);
    /// vec.push(5);
    /// assert_eq!(vec.capacity(), 8);
    /// ```
    pub const fn capacity(&self) -> usize {
        self.capacity
    }
    /// Returns a reference to the element at the given index or `None` if the index is out of bounds.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            Some(&self[index])
        } else {
            None
        }
    }
    /// Returns a mutable reference to the element at the given index or `None` if the index is out of bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            Some(&mut self[index])
        } else {
            None
        }
    }
    /// Returns an iterator over references of the elements in the `MyVec`.
    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }
    /// Returns an iterator over mutable references of the elements in the `MyVec`.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.into_iter()
    }
    /// Returns the layout for the current allocation.
    fn layout(&self) -> core::alloc::Layout {
        unsafe {
            core::alloc::Layout::from_size_align_unchecked(
                self.capacity * std::mem::size_of::<T>(),
                std::mem::align_of::<T>(),
            )
        }
    }
    fn realloc_if_necessary(&mut self) {
        if self.capacity == self.len {
            self.realloc_with_capacity(2.max(self.capacity * 2))
        }
    }
    /// Reallocs `MyVec` with a new capacity.
    ///
    /// If the current capacity is 0, an `alloc` is performed instead.
    fn realloc_with_capacity(&mut self, capacity: usize) {
        let new_size = capacity * std::mem::size_of::<T>();
        // If the new size is 0, do nothing.
        // Avoids problems with ZSTs.
        if new_size == 0 {
            return;
        }

        // SAFETY: Size and alignment are correct
        let alloc = unsafe {
            if self.capacity == 0 {
                std::alloc::alloc(core::alloc::Layout::from_size_align_unchecked(
                    new_size,
                    std::mem::align_of::<T>(),
                ))
            } else {
                std::alloc::realloc(self.ptr.as_ptr() as *mut u8, self.layout(), new_size)
            }
        };
        if alloc.is_null() {
            std::alloc::handle_alloc_error(self.layout());
        }
        // SAFETY: Pointer is not null
        unsafe {
            self.ptr = core::ptr::NonNull::new_unchecked(alloc as *mut T);
        }

        self.capacity = capacity;
    }
}

impl<T> Default for MyVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for MyVec<T> {
    fn drop(&mut self) {
        // SAFETY: Pointer is not null if capacity > 0
        if self.capacity > 0 {
            unsafe {
                std::alloc::dealloc(self.ptr.as_ptr() as *mut u8, self.layout());
            }
        }
    }
}

impl<T> Extend<T> for MyVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        {
            let (min, max) = iter.size_hint();
            let reserve = max.unwrap_or(min);
            self.reserve(reserve);
        }
        for item in iter {
            self.push(item);
        }
    }
}

impl<T> FromIterator<T> for MyVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = Self::new();
        vec.extend(iter);
        vec
    }
}

impl<T> AsRef<[T]> for MyVec<T> {
    fn as_ref(&self) -> &[T] {
        // SAFETY: Pointer is usable even if len == 0, NonNull::dangling() is a valid pointer for empty slices
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> AsMut<[T]> for MyVec<T> {
    fn as_mut(&mut self) -> &mut [T] {
        // SAFETY: Pointer is usable even if len == 0, NonNull::dangling() is a valid pointer for empty slices
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}

impl<T, S> PartialEq<S> for MyVec<T>
where
    S: AsRef<[T]>,
    T: PartialEq,
{
    fn eq(&self, other: &S) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T, S> PartialOrd<S> for MyVec<T>
where
    S: AsRef<[T]>,
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &S) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl<T, Idx> core::ops::Index<Idx> for MyVec<T>
where
    Idx: core::slice::SliceIndex<[T]>,
{
    type Output = <Idx as core::slice::SliceIndex<[T]>>::Output;
    fn index(&self, index: Idx) -> &Self::Output {
        self.as_ref().index(index)
    }
}

impl<T, Idx> core::ops::IndexMut<Idx> for MyVec<T>
where
    Idx: core::slice::SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.as_mut().index_mut(index)
    }
}

impl<T> core::fmt::Debug for MyVec<T>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.as_ref().iter()).finish()
    }
}

impl<T> Clone for MyVec<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        MyVec::from_iter(self.as_ref().iter().cloned())
    }
}

/// An iterator over the elements of a `MyVec`.
///
/// # Example
/// ```
/// use mycollections::MyVec;
///
/// let vec = MyVec::from_iter(0..=2);
/// assert_eq!(vec, [0, 1, 2]);
/// let mut iter = vec.into_iter();
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone)]
pub struct IntoIter<T> {
    vec: MyVec<T>,
    index: usize,
}

/// An iterator over references of the elements of a `MyVec`.
///
/// # Example
/// ```
/// use mycollections::MyVec;
///
/// let vec = MyVec::from_iter(0..=2);
/// assert_eq!(vec, [0, 1, 2]);
/// let mut iter = vec.iter();
/// assert_eq!(iter.next(), Some(&0));
/// assert_eq!(iter.next(), Some(&1));
/// assert_eq!(iter.next(), Some(&2));
/// assert_eq!(iter.next(), None);
/// ```
pub struct Iter<'a, T> {
    vec: &'a MyVec<T>,
    index: usize,
}

/// An iterator over mutable references of the elements of a `MyVec`.
///
/// # Example
/// ```
/// use mycollections::MyVec;
///
/// let mut vec = MyVec::from_iter(0..=2);
/// assert_eq!(vec, [0, 1, 2]);
/// for item in vec.iter_mut() {
///     *item *= 2;
/// }
/// assert_eq!(vec, [0, 2, 4]);
/// ```
pub struct IterMut<'a, T> {
    vec: &'a mut MyVec<T>,
    index: usize,
}

/// An iterator over the elements of a `MyVec`.
/// 
/// Each time `next` is called, the iterator removes the element from the `MyVec`.
/// 
/// This iterator should be created with the [`MyVec::drain`] method.
pub struct Drain<'a, T> {
    vec: &'a mut MyVec<T>,
    start: usize,
    elements: usize,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.vec.len {
            return None;
        }
        let ptr = unsafe { self.vec.ptr.as_ptr().add(self.index) };
        self.index += 1;
        unsafe { Some(ptr.read()) }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vec.len - self.index;
        (remaining, Some(remaining))
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.index += 1;
        self.vec.get(self.index - 1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vec.len - self.index;
        (remaining, Some(remaining))
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.vec.len {
            return None;
        }
        // SAFETY: index < vec.len
        let ptr = unsafe { self.vec.ptr.as_ptr().add(self.index) };
        self.index += 1;
        // SAFETY: pointer is valid and points to the MyVec allocation
        unsafe { Some(&mut *ptr) }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vec.len - self.index;
        (remaining, Some(remaining))
    }
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.elements == 0 {
            return None
        }
        self.elements -= 1;
        Some(self.vec.remove(self.start))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.elements, Some(self.elements))
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}
impl<T> ExactSizeIterator for Iter<'_, T> {}
impl<T> ExactSizeIterator for IterMut<'_, T> {}
impl<T> ExactSizeIterator for Drain<'_, T> {}

impl<T> IntoIterator for MyVec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            vec: self,
            index: 0,
        }
    }
}

impl<'a, T> IntoIterator for &'a MyVec<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            vec: self,
            index: 0,
        }
    }
}

impl<'a, T> IntoIterator for &'a mut MyVec<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            vec: self,
            index: 0,
        }
    }
}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        for _ in self {}
    }
}
