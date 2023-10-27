type T = u32;
pub struct MyVec {
    len: usize,
    capacity: usize,
    ptr: core::ptr::NonNull<T>,
}

impl MyVec {
    /// Creates a new `MyVec`
    /// # Example
    /// ```
    /// use myvec::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// ```
    pub fn new() -> MyVec {
        MyVec {
            len: 0,
            capacity: 0,
            ptr: std::ptr::NonNull::dangling(),
        }
    }
    /// Adds a new element to the `MyVec`
    /// # Example
    /// ```
    /// use myvec::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec[0], 1);
    /// assert_eq!(vec[1], 2);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    pub fn push(&mut self, value: T) {
        if self.capacity == 0 {
            self.realloc_with_capacity(1);
        } else if self.capacity == self.len {
            self.realloc_with_capacity(self.capacity * 2)
        }
        unsafe {
            self.ptr.as_ptr().add(self.len).write(value);
        }
        self.len += 1;
    }
    /// Removes the last element from the `MyVec` and returns it.
    ///
    /// If the `MyVec` is empty, `None` is returned
    ///
    /// # Example
    /// ```
    /// use myvec::MyVec;
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
    /// Returns the length of the `MyVec`
    /// # Example
    /// ```
    /// use myvec::MyVec;
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
    /// use myvec::MyVec;
    ///
    /// let mut vec = MyVec::new();
    /// vec.push(1);
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
    pub fn reserve(&mut self, additional: usize) {
        if self.capacity < self.len + additional {
            self.realloc_with_capacity(self.len + additional)
        }
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
    /// Reallocs `MyVec` with a new capacity.
    ///
    /// If the current capacity is 0, an `alloc` is performed instead.
    fn realloc_with_capacity(&mut self, capacity: usize) {
        let new_size = capacity * std::mem::size_of::<T>();
        
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

impl Default for MyVec {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for MyVec {
    fn drop(&mut self) {
        if self.capacity > 0 {
            unsafe {
                std::alloc::dealloc(self.ptr.as_ptr() as *mut u8, self.layout());
            }
        }
    }
}

impl Extend<T> for MyVec {
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

impl FromIterator<T> for MyVec {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = Self::new();
        vec.extend(iter);
        vec
    }
}

impl AsRef<[T]> for MyVec {
    fn as_ref(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl AsMut<[T]> for MyVec {
    fn as_mut(&mut self) -> &mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}

impl<S> PartialEq<S> for MyVec
where
    S: AsRef<[T]>,
{
    fn eq(&self, other: &S) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<S> PartialOrd<S> for MyVec
where
    S: AsRef<[T]>,
{
    fn partial_cmp(&self, other: &S) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl core::ops::Index<usize> for MyVec {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.ptr.as_ptr().add(index).as_ref().unwrap_unchecked() }
    }
}

impl core::fmt::Debug for MyVec {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.as_ref().iter()).finish()
    }
}
