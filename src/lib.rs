//! # rancor
//!
//! rancor provides scalable and efficient error handling without using type
//! composition. This makes it best-suited for situations where:
//!
//! - Programmatic error introspection is not useful
//! - Functions may error, but succeed most of the time
//! - Errors should provide as much useful detail as possible when emitted
//! - Use cases include both `no_std` and targets with support for `std`

#![deny(
    future_incompatible,
    missing_docs,
    nonstandard_style,
    unsafe_op_in_unsafe_fn,
    unused,
    warnings,
    clippy::all,
    clippy::missing_safety_doc,
    clippy::undocumented_unsafe_blocks,
    rustdoc::broken_intra_doc_links,
    rustdoc::missing_crate_level_docs
)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
mod boxed_error;
#[cfg(feature = "alloc")]
mod thin_box;

use core::fmt;

#[cfg(feature = "std")]
use std::error::Error as StdError;

#[cfg(not(feature = "std"))]
/// An error that can be debugged and displayed.
///
/// Without the `std` feature enabled, this has supertraits of
/// [`core::fmt::Debug`] and [`core::fmt::Display`]. With the `std`
/// feature enabled, this also has a supertrait of [`std::error::Error`]
/// instead.
///
/// This trait is always `Send + Sync + 'static`.
#[cfg_attr(feature = "alloc", ptr_meta::pointee)]
pub trait StdError: fmt::Debug + fmt::Display {
    /// The lower-level source of this error, if any.
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        None
    }
}

#[cfg(not(feature = "std"))]
impl<T: fmt::Debug + fmt::Display + ?Sized> StdError for T {}

/// An error type which can be uniformly constructed from a [`StdError`].
pub trait Error: Sized + StdError + Send + Sync + 'static {
    /// Returns a new `Self` using the given [`Error`].
    ///
    /// Depending on the specific implementation, this may box the error,
    /// immediately emit a diagnostic, or discard it and only remember that some
    /// error occurred.
    fn new<T: StdError + Send + Sync + 'static>(source: T) -> Self;

    /// Returns a new `Self` using the [`Error`] returned by calling
    /// `make_source`.
    ///
    /// Depending on the specific implementation, this may box the error or
    /// discard it and only remember that some error occurred.
    fn new_with<T, F>(make_source: F) -> Self
    where
        T: StdError + Send + Sync + 'static,
        F: FnOnce() -> T,
    {
        Self::new(make_source())
    }

    /// Adds additional context to this error, returning a new error.
    fn context<T: fmt::Debug + fmt::Display + Send + Sync + 'static>(self, context: T) -> Self;
}

/// A type that can produce an error.
pub trait Fallible {
    /// The error produced by any failing methods.
    type Error: Error;
}

/// A validation context that simply records success or failure, throwing away
/// any detailed error messages.
#[derive(Debug)]
pub struct Failure;

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to check bytes")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Failure {}

impl Error for Failure {
    fn new<T: fmt::Display>(_: T) -> Self {
        Self
    }

    fn new_with<T: fmt::Display, F: FnOnce() -> T>(_: F) -> Self {
        Self
    }

    fn context<T: fmt::Display>(self, _: T) -> Self {
        self
    }
}

impl Fallible for Failure {
    type Error = Self;
}

#[cfg(feature = "alloc")]
pub use boxed_error::BoxedError;

#[cfg(feature = "alloc")]
impl Fallible for BoxedError {
    type Error = Self;
}
