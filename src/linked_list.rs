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
    pub const fn new() -> LinkedList<T> {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            _marker: std::marker::PhantomData,
        }
    }
    /// Pushes a new element to the end of the `LinkedList`.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    /// assert_eq!(list, [0, 1, 2]);
    /// ```
    pub fn push_back(&mut self, value: T) {
        let node = Some(Node::new(value, self.tail, None));
        self.tail = node;
        if self.head.is_none() {
            self.head = node;
        }
        self.len += 1;
    }
    /// Pushes a new element to the front of the `LinkedList`.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// list.push_front(0);
    /// list.push_front(1);
    /// list.push_front(2);
    /// assert_eq!(list, [2, 1, 0]);
    /// ```
    pub fn push_front(&mut self, value: T) {
        let node = Some(Node::new(value, None, self.head));
        self.head = node;
        if self.tail.is_none() {
            self.tail = node;
        }
        self.len += 1;
    }
    /// Removes the last element of the `LinkedList` and returns it.
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
        // SAFETY: If `self.tail` is `Some`, then it's valid.
        let tail = unsafe { Node::dealloc(self.tail?) };
        self.len -= 1;
        self.tail = tail.prev;
        if self.len <= 1 {
            self.head = tail.prev;
        }
        Some(tail.remove())
    }
    /// Removes the first element of the `LinkedList` and returns it.
    ///
    /// If the `LinkedList` is empty, `None` is returned.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list = LinkedList::from_iter(0..=2);
    /// assert_eq!(list.pop_front(), Some(0));
    /// assert_eq!(list.pop_front(), Some(1));
    /// assert_eq!(list.pop_front(), Some(2));
    /// assert_eq!(list.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        // SAFETY: If `self.head` is `Some`, then it's valid.
        let head = unsafe { Node::dealloc(self.head?) };
        self.len -= 1;
        self.head = head.next;
        if self.len <= 1 {
            self.tail = head.next;
        }
        Some(head.remove())
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
    /// Returns an iterator over mutable references of the elements in the `LinkedList`.
    ///
    /// # Example
    /// ```
    /// use mycollections::LinkedList;
    ///
    /// let mut list = LinkedList::from_iter(0..=2);
    /// for item in list.iter_mut() {
    ///     *item *= 2;
    /// }
    /// assert_eq!(list, [0, 2, 4]);
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
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
    /// list.push_back(1);
    /// assert_eq!(list.is_empty(), false);
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Node<T> {
    /// Creates and allocates a new `Node<T>` with the given `value`.
    ///
    /// It correctly handles insertions if `prev` and `next` are provided.
    fn new(value: T, prev: Option<NodeBox<T>>, next: Option<NodeBox<T>>) -> NodeBox<T> {
        let layout = core::alloc::Layout::new::<Node<T>>();
        let node = Node { value, prev, next };
        let alloc = crate::alloc_array::<Node<T>>(1).unwrap_or(core::ptr::NonNull::dangling());
        // SAFETY: Pointer is valid and aligned; With ZSTs ptr::write is a no-op
        unsafe { alloc.as_ptr().write(node) };

        // Handle insertion
        // SAFETY: If `prev` and `next` are `Some`, then they are valid
        if let Some(mut prev) = prev {
            let prev = unsafe { prev.as_mut() };
            prev.next = Some(alloc);
        }
        if let Some(mut next) = next {
            let next = unsafe { next.as_mut() };
            next.prev = Some(alloc);
        }
        alloc
    }
    /// Removes the `Node<T>` from the `LinkedList` and returns its value.
    ///
    /// Updates the `prev` and `next` links accordingly:
    /// - `prev.next = self.next`
    /// - `next.prev = self.prev`
    fn remove(self) -> T {
        // SAFETY: If `self.prev` and `self.next` are `Some`, then they are valid
        if let Some(mut prev) = self.prev {
            let prev = unsafe { prev.as_mut() };
            prev.next = self.next;
        }
        if let Some(mut next) = self.next {
            let next = unsafe { next.as_mut() };
            next.prev = self.prev;
        }
        self.value
    }
    /// Deallocates the `NodeBox<T>` and returns the `Node<T>` it contains.
    unsafe fn dealloc(node: NodeBox<T>) -> Node<T> {
        let nodeptr = node.as_ptr();
        let node = nodeptr.read();
        unsafe { std::alloc::dealloc(nodeptr as *mut u8, core::alloc::Layout::new::<Node<T>>()) };
        node
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

impl<T> Clone for LinkedList<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        LinkedList::from_iter(self.iter().cloned())
    }
}

impl<T> Extend<T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.push_back(value)
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
pub struct Iter<'a, T> {
    current: Option<NodeBox<T>>,
    len: usize,
    _marker: std::marker::PhantomData<&'a T>,
}
/// An iterator over mutable references of the elements in the `LinkedList`.
///
/// # Example
/// ```
/// use mycollections::LinkedList;
///
/// let mut list = LinkedList::from_iter(0..=2);
/// for item in &mut list {
///     *item *= 2;
/// }
/// assert_eq!(list, [0, 2, 4]);
/// ```
pub struct IterMut<'a, T> {
    current: Option<NodeBox<T>>,
    len: usize,
    _marker: std::marker::PhantomData<&'a mut T>,
}
/// An iterator over the elements in the `LinkedList`.
///
/// # Example
/// ```
/// use mycollections::LinkedList;
///
/// let mut list = LinkedList::from_iter(0..=2);
/// let mut iter = list.into_iter();
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), None);
/// ```
pub struct IntoIter<T> {
    list: LinkedList<T>,
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
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        let current = unsafe { self.current?.as_mut() };
        self.current = current.next;
        self.len -= 1;
        Some(&mut current.value)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}
impl<'a, T> ExactSizeIterator for IterMut<'a, T> {}
impl<T> ExactSizeIterator for IntoIter<T> {}

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
impl<'a, T> IntoIterator for &'a mut LinkedList<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            current: self.head,
            len: self.len,
            _marker: std::marker::PhantomData,
        }
    }
}
impl<T> IntoIterator for LinkedList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter { list: self }
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        for item in iter {
            list.push_back(item);
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
        self.iter().eq(other.as_ref())
    }
}

impl<T> PartialOrd for LinkedList<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> std::option::Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T, Slice> PartialOrd<Slice> for LinkedList<T>
where
    T: PartialOrd,
    Slice: AsRef<[T]>,
{
    fn partial_cmp(&self, other: &Slice) -> std::option::Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.as_ref())
    }
}

impl<T> Eq for LinkedList<T> where T: Eq {}
impl<T> Ord for LinkedList<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zst() {
        let mut list = LinkedList::<()>::new();
        list.push_back(());
        assert_eq!(list.len(), 1);
        assert_eq!(list, [()]);
        assert_eq!(list.pop_back(), Some(()));
        assert_eq!(list.len(), 0);

        list.extend((0..5).map(|_| ()));
        assert_eq!(list.len(), 5);
        assert_eq!(list, [(); 5]);
        assert_eq!(list.pop_front(), Some(()));
        assert_eq!(list.pop_back(), Some(()));
        assert_eq!(list.len(), 3);

        let mut iter = list.into_iter();
        assert_eq!(iter.next(), Some(()));
        assert_eq!(iter.next(), Some(()));
        assert_eq!(iter.next(), Some(()));
        assert_eq!(iter.next(), None);
    }
}
