/// My implementation of `LinkedList`.
/// 
/// Implemented methods should behave exactly like the original.
pub struct LinkedList<T> {
    head: Option<core::ptr::NonNull<Node<T>>>,
    tail: Option<core::ptr::NonNull<Node<T>>>,
    len: usize,
    marker: std::marker::PhantomData<Box<Node<T>>>,
}

struct Node<T> {
    value: T,
    next: Option<core::ptr::NonNull<Node<T>>>,
    prev: Option<core::ptr::NonNull<Node<T>>>,
}