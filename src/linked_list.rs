//! My implementation of Rust's [`LinkedList`](std::collections::LinkedList).
//!
//! Implemented methods should behave exactly like the original.

type NodeBox<T> = core::ptr::NonNull<Node<T>>;

/// My implementation of `LinkedList`.
///
/// Implemented methods should behave exactly like the original.
pub struct LinkedList<T> {
    head: Option<NodeBox<T>>,
    tail: Option<NodeBox<T>>,
    len: usize,
    _marker: std::marker::PhantomData<Box<Node<T>>>,
}

#[derive(Default)]
struct Node<T> {
    value: T,
    next: Option<NodeBox<T>>,
    prev: Option<NodeBox<T>>,
}

impl<T> LinkedList<T> {
    /// Creates a new `LinkedList`
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list: LinkedList<i32> = LinkedList::new();
    /// assert_eq!(list.len(), 0);
    /// assert_eq!(list.pop_back(), None);
    /// assert_eq!(list, []);
    /// ```
    pub fn new() -> LinkedList<T> {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            _marker: std::marker::PhantomData,
        }
    }
    /// Pushes a new element to the end of the `LinkedList`.
    pub fn push(&mut self, value: T) {
        let node = Some(Node::new(value, self.tail, None));
        if self.tail.is_some() {
            self.tail = node;
        } else {
            self.head = node;
            self.tail = node;
        }
        self.len += 1;
    }
    /// Pops the last element from the `LinkedList` and returns it.
    ///
    /// If the `LinkedList` is empty, `None` is returned.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list = LinkedList::from_iter(0..=2);
    /// assert_eq!(list.pop_back(), Some(2));
    /// assert_eq!(list.pop_back(), Some(1));
    /// assert_eq!(list.pop_back(), Some(0));
    /// assert_eq!(list.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        let tailptr = self.tail?.as_ptr();
        // SAFETY: If `self.tail` is `Some`, then it's valid.
        let tail = unsafe { tailptr.read() };
        unsafe { std::alloc::dealloc(tailptr as *mut u8, core::alloc::Layout::new::<Node<T>>()) };

        self.len -= 1;
        if self.len == 0 {
            self.tail = None;
            self.head = None;
            Some(tail.remove())
        } else if self.len == 1 {
            self.tail = tail.prev;
            self.head = tail.prev;
            Some(tail.remove())
        } else {
            self.tail = tail.prev;
            Some(tail.remove())
        }
    }
    /// Returns an iterator over references of the elements in the `LinkedList`.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list = LinkedList::from_iter(0..=2);
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }
    /// Returns the lenght of the list.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let list = LinkedList::from_iter(0..=2);
    /// assert_eq!(list.len(), 3);
    /// ```
    pub const fn len(&self) -> usize {
        self.len
    }
    /// Returns `true` if the list is empty.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.is_empty(), true);
    /// list.push(1);
    /// assert_eq!(list.is_empty(), false);
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Node<T> {
    /// Creates and allocates a new `Node<T>` with the given `value`.
    fn new(value: T, prev: Option<NodeBox<T>>, next: Option<NodeBox<T>>) -> NodeBox<T> {
        let layout = core::alloc::Layout::new::<Node<T>>();
        let node = Node { value, prev, next };
        // SAFETY: Size and alignment are correct
        let alloc = unsafe { std::alloc::alloc(layout) } as *mut Node<T>;
        if alloc.is_null() {
            std::alloc::handle_alloc_error(layout)
        }
        // SAFETY: Pointer is valid and aligned
        unsafe {
            alloc.write(node);
        }
        // SAFETY: Pointer is not null
        let alloc = unsafe { core::ptr::NonNull::new_unchecked(alloc) };
        // Handle insertion
        let prev = prev.map(|mut p| unsafe { p.as_mut() });
        let next = next.map(|mut n| unsafe { n.as_mut() });
        match (prev, next) {
            (None, Some(next)) => next.prev = Some(alloc),
            (Some(prev), None) => prev.next = Some(alloc),
            (Some(prev), Some(next)) => {
                prev.next = Some(alloc);
                next.prev = Some(alloc);
            }
            (None, None) => {}
        }
        alloc
    }
    fn remove(self) -> T {
        let prev = self.prev.map(|mut p| unsafe { p.as_mut() });
        let next = self.next.map(|mut n| unsafe { n.as_mut() });
        match (prev, next) {
            (None, Some(next)) => next.prev = None,
            (Some(prev), None) => prev.next = None,
            (Some(prev), Some(next)) => {
                prev.next = self.next;
                next.prev = self.prev;
            }
            (None, None) => {}
        }
        self.value
    }
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> AsRef<T> for Node<T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<T> core::fmt::Debug for LinkedList<T>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T> core::fmt::Debug for Node<T>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // SAFETY: If `prev` and `next` are `Some`, then they are valid
        let prev = self.prev.map(|p| unsafe { p.as_ref() });
        let next = self.next.map(|n| unsafe { n.as_ref() });
        f.debug_struct("Node")
            .field("value", &self.value)
            .field("prev", &prev)
            .field("next", &next)
            .finish()
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        while let Some(headptr) = self.head {
            let head = unsafe { headptr.as_ref() };
            self.head = head.next;
            unsafe {
                std::alloc::dealloc(
                    headptr.as_ptr() as *mut u8,
                    core::alloc::Layout::new::<Node<T>>(),
                )
            };
        }
    }
}

/// An iterator over references of the elements in the `LinkedList`.
///
/// # Example
/// ```
/// use mycollections::LinkedList;
///
/// let mut list = LinkedList::from_iter(0..=2);
/// let mut iter = list.iter();
/// assert_eq!(iter.next(), Some(&0));
/// assert_eq!(iter.next(), Some(&1));
/// assert_eq!(iter.next(), Some(&2));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Debug)]
pub struct Iter<'a, T> {
    current: Option<NodeBox<T>>,
    len: usize,
    _marker: std::marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        let current = unsafe { self.current?.as_ref() };
        self.current = current.next;
        self.len -= 1;
        Some(&current.value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}
impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T> IntoIterator for &'a LinkedList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            current: self.head,
            len: self.len,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        for item in iter {
            list.push(item);
        }
        list
    }
}

impl<T> PartialEq for LinkedList<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T, Slice> PartialEq<Slice> for LinkedList<T>
where
    T: PartialEq,
    Slice: AsRef<[T]>,
{
    fn eq(&self, other: &Slice) -> bool {
        self.iter().eq(other.as_ref().iter())
    }
}

impl<T> PartialOrd for LinkedList<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> std::option::Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T, Slice> PartialOrd<Slice> for LinkedList<T>
where
    T: PartialOrd,
    Slice: AsRef<[T]>,
{
    fn partial_cmp(&self, other: &Slice) -> std::option::Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.as_ref().iter())
    }
}
