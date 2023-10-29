#![deny(missing_docs)]

//! My own implementations of the data structures in the Rust `std::collections` module.
//! 
//! All methods and structs are fully documented (enforced by `#[deny(missing_docs)]`).
//! 
//! Currently implemented:
//! - `Vec`

mod vec;
mod linked_list;
pub use vec::*;
pub use linked_list::*;
