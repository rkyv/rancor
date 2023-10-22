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

use core::{fmt, hint::unreachable_unchecked};

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

/// An error type which can be given additional context.
pub trait Contextual: Sized + Send + Sync + 'static {
    /// Adds additional context to this error, returning a new error.
    fn add_context<T>(self, context: T) -> Self
    where
        T: fmt::Debug + fmt::Display + Send + Sync + 'static;
}

/// An error type which can be uniformly constructed from a [`StdError`].
pub trait Error: Contextual + StdError {
    /// Returns a new `Self` using the given [`Error`].
    ///
    /// Depending on the specific implementation, this may box the error,
    /// immediately emit a diagnostic, or discard it and only remember that some
    /// error occurred.
    fn new<T: StdError + Send + Sync + 'static>(source: T) -> Self;
}

/// Helper methods for `Context`s.
pub trait Context {
    /// Wraps the error value of this type with additional context.
    fn context<C>(self, context: C) -> Self
    where
        C: fmt::Debug + fmt::Display + Send + Sync + 'static;

    /// Wraps the error value of this type with additional context. The
    /// additional context is evaluated only if an error occurred.
    fn with_context<C, F>(self, f: F) -> Self
    where
        C: fmt::Debug + fmt::Display + Send + Sync + 'static,
        F: FnOnce() -> C;
}

impl<T, E> Context for Result<T, E>
where
    E: Contextual,
{
    fn context<C>(self, context: C) -> Self
    where
        C: fmt::Debug + fmt::Display + Send + Sync + 'static,
    {
        match self {
            x @ Ok(_) => x,
            Err(e) => Err(e.add_context(context)),
        }
    }

    fn with_context<C, F>(self, f: F) -> Self
    where
        C: fmt::Debug + fmt::Display + Send + Sync + 'static,
        F: FnOnce() -> C,
    {
        match self {
            x @ Ok(_) => x,
            Err(e) => Err(e.add_context(f())),
        }
    }
}

pub use core::convert::Infallible;

impl Contextual for Infallible {
    fn add_context<T>(self, _: T) -> Self
    where
        T: fmt::Debug + fmt::Display + Send + Sync + 'static,
    {
        // SAFETY: `Infallible` is an enum with no variants, and so can never be
        // constructed as the `self` parameter.
        unsafe {
            unreachable_unchecked();
        }
    }
}

/// An error type that does not occupy any space, panicking on creation instead.
#[derive(Debug)]
pub enum Panic {}

impl fmt::Display for Panic {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        // SAFETY: `Panic` is an enum with no variants, and so can never be
        // constructed as the `self` parameter.
        unsafe {
            unreachable_unchecked();
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Panic {}

impl Contextual for Panic {
    fn add_context<T>(self, _: T) -> Self
    where
        T: fmt::Debug + fmt::Display + Send + Sync + 'static,
    {
        // SAFETY: `Panic` is an enum with no variants, and so can never be
        // constructed as the `self` parameter.
        unsafe {
            unreachable_unchecked();
        }
    }
}

impl Error for Panic {
    fn new<T: fmt::Display>(error: T) -> Self {
        panic!("created a new `Panic` from: {error}");
    }
}

/// An error type that only preserves success or failure, throwing away any more
/// detailed error messages.
#[derive(Debug)]
pub struct Failure;

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to check bytes")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Failure {}

impl Contextual for Failure {
    fn add_context<T: fmt::Display>(self, _: T) -> Self {
        self
    }
}

impl Error for Failure {
    fn new<T: fmt::Display>(_: T) -> Self {
        Self
    }
}

#[cfg(feature = "alloc")]
pub use boxed_error::BoxedError;
