//! My implementation of Rust's [`Vec`](std::vec::Vec).
//!
//! Implemented methods should behave exactly like the original.

/// My implementation of Rust's [`Vec`](std::vec::Vec).
///
/// Implemented methods should behave exactly like the original.
pub struct Vec<T> {
    len: usize,
    capacity: usize,
    ptr: core::ptr::NonNull<T>,
    /// Needed to ensure that we own the data, see [`core::ptr::Unique`]
    _marker: core::marker::PhantomData<T>,
}

impl<T> Vec<T> {
    /// Creates a new `Vec`
    /// # Example
    /// ```
    /// use mycollections::Vec;
    ///
    /// let mut vec: Vec<i32> = Vec::new();
    /// ```
    pub const fn new() -> Vec<T> {
        Vec {
            len: 0,
            capacity: 0,
            ptr: std::ptr::NonNull::dangling(),
            _marker: core::marker::PhantomData,
        }
    }
    /// Reserves capacity for at least `additional` more elements to be inserted in the `Vec`.
    ///
    /// New capacity will be the next power of two large enough to hold the additional elements.
    ///
    /// If `T` is a ZST, the `Vec`'s capacity is always 0, so this will do nothing.
    ///
    /// # Example
    /// ```
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::<u8>::new();
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
    /// Adds a new element to the `Vec`
    /// # Example
    /// ```
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::new();
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
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::new();
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
    /// Removes the last element from the `Vec` and returns it.
    ///
    /// If the `Vec` is empty, `None` is returned
    ///
    /// # Example
    /// ```
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::new();
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
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::from_iter(0..5);
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
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::from_iter(0..=4);
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
    pub fn drain(&mut self, range: impl core::ops::RangeBounds<usize>) -> Drain<T> {
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
    /// Returns the length of the `Vec`
    /// # Example
    /// ```
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.len(), 2);
    /// ```
    pub const fn len(&self) -> usize {
        self.len
    }
    /// Returns `true` if the `Vec` is empty
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// Returns the capacity of the `Vec`
    /// # Example
    /// ```
    /// use mycollections::Vec;
    ///
    /// let mut vec = Vec::new();
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
    /// Returns an iterator over references of the elements in the `Vec`.
    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }
    /// Returns an iterator over mutable references of the elements in the `Vec`.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.into_iter()
    }
    fn realloc_if_necessary(&mut self) {
        if self.capacity == self.len {
            self.realloc_with_capacity(2.max(self.capacity * 2))
        }
    }
    /// Reallocs `Vec` with a new capacity.
    ///
    /// If the current capacity is 0, an `alloc` is performed instead.
    fn realloc_with_capacity(&mut self, capacity: usize) {
        if let Some(ptr) = crate::realloc_array(self.ptr, self.capacity, capacity) {
            self.ptr = ptr;
            self.capacity = capacity;
        }
    }
}

impl<T> Default for Vec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for Vec<T> {
    fn drop(&mut self) {
        crate::dealloc_array(self.ptr, self.capacity)
    }
}

impl<T> Extend<T> for Vec<T> {
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

impl<T> FromIterator<T> for Vec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = Self::new();
        vec.extend(iter);
        vec
    }
}

impl<T> AsRef<[T]> for Vec<T> {
    fn as_ref(&self) -> &[T] {
        // SAFETY: Pointer is usable even if len == 0, NonNull::dangling() is a valid pointer for empty slices
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> AsMut<[T]> for Vec<T> {
    fn as_mut(&mut self) -> &mut [T] {
        // SAFETY: Pointer is usable even if len == 0, NonNull::dangling() is a valid pointer for empty slices
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}

impl<T, S> PartialEq<S> for Vec<T>
where
    S: AsRef<[T]>,
    T: PartialEq,
{
    fn eq(&self, other: &S) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T, S> PartialOrd<S> for Vec<T>
where
    S: AsRef<[T]>,
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &S) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl<T, Idx> core::ops::Index<Idx> for Vec<T>
where
    Idx: core::slice::SliceIndex<[T]>,
{
    type Output = <Idx as core::slice::SliceIndex<[T]>>::Output;
    fn index(&self, index: Idx) -> &Self::Output {
        self.as_ref().index(index)
    }
}

impl<T, Idx> core::ops::IndexMut<Idx> for Vec<T>
where
    Idx: core::slice::SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.as_mut().index_mut(index)
    }
}

impl<T> core::fmt::Debug for Vec<T>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.as_ref().iter()).finish()
    }
}

impl<T> Clone for Vec<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Vec::from_iter(self.as_ref().iter().cloned())
    }
}

/// An iterator over the elements of a `Vec`.
///
/// # Example
/// ```
/// use mycollections::Vec;
///
/// let vec = Vec::from_iter(0..=2);
/// assert_eq!(vec, [0, 1, 2]);
/// let mut iter = vec.into_iter();
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone)]
pub struct IntoIter<T> {
    vec: Vec<T>,
    index: usize,
}

/// An iterator over references of the elements of a `Vec`.
///
/// # Example
/// ```
/// use mycollections::Vec;
///
/// let vec = Vec::from_iter(0..=2);
/// assert_eq!(vec, [0, 1, 2]);
/// let mut iter = vec.iter();
/// assert_eq!(iter.next(), Some(&0));
/// assert_eq!(iter.next(), Some(&1));
/// assert_eq!(iter.next(), Some(&2));
/// assert_eq!(iter.next(), None);
/// ```
pub struct Iter<'a, T> {
    vec: &'a Vec<T>,
    index: usize,
}

/// An iterator over mutable references of the elements of a `Vec`.
///
/// # Example
/// ```
/// use mycollections::Vec;
///
/// let mut vec = Vec::from_iter(0..=2);
/// assert_eq!(vec, [0, 1, 2]);
/// for item in vec.iter_mut() {
///     *item *= 2;
/// }
/// assert_eq!(vec, [0, 2, 4]);
/// ```
pub struct IterMut<'a, T> {
    vec: &'a mut Vec<T>,
    index: usize,
}

/// An iterator over the elements of a `Vec`.
///
/// Each time `next` is called, the iterator removes the element from the `Vec`.
///
/// This iterator should be created with the [`Vec::drain`] method.
pub struct Drain<'a, T> {
    vec: &'a mut Vec<T>,
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
        // SAFETY: pointer is valid and points to the Vec allocation
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
            return None;
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

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            vec: self,
            index: 0,
        }
    }
}

impl<'a, T> IntoIterator for &'a Vec<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            vec: self,
            index: 0,
        }
    }
}

impl<'a, T> IntoIterator for &'a mut Vec<T> {
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn zst() {
        let mut vec = Vec::<()>::new();
        assert_eq!(vec.len(), 0);
        assert!(vec.is_empty());
        assert_eq!(vec.capacity, 0);
        vec.push(());
        assert_eq!(vec.len(), 1);
        assert!(!vec.is_empty());
        assert_eq!(vec.capacity, 0);
        vec.extend((0..5).map(|_| ()));
        assert_eq!(vec.len(), 6);
        assert!(!vec.is_empty());
        assert_eq!(vec.capacity, 0);

        assert_eq!(vec, [(); 6])
    }
}
