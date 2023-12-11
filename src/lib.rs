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

use core::{
    fmt,
    hint::unreachable_unchecked,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

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

/// A type which can add an additional trace to itself.
pub trait Traceable: Sized + Send + Sync + 'static {
    /// Adds an additional trace to this error, returning a new error.
    fn add_trace<R>(self, trace: R) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static;
}

/// An error type which can be uniformly constructed from a [`StdError`] and
/// given additional context.
pub trait Error: Traceable + StdError {
    /// Returns a new `Self` using the given [`Error`].
    ///
    /// Depending on the specific implementation, this may box the error,
    /// immediately emit a diagnostic, or discard it and only remember that some
    /// error occurred.
    fn new<T: StdError + Send + Sync + 'static>(source: T) -> Self;
}

/// A type with fallible operations that return its associated error type.
pub trait Fallible {
    /// The error type associated with this type's operations.
    type Error;
}

/// Equips a type with a `Fallible` implementation that chooses `E` as its error
/// type.
#[repr(transparent)]
pub struct Strategy<T: ?Sized, E> {
    _error: PhantomData<E>,
    inner: T,
}

impl<T, E> Fallible for Strategy<T, E> {
    type Error = E;
}

impl<T: ?Sized, E> Strategy<T, E> {
    /// Wraps the given mutable reference, returning a mutable reference to a
    /// `Strategy`.
    pub fn wrap(inner: &mut T) -> &mut Self {
        // SAFETY: `Strategy` is `repr(transparent)` and so has the same layout
        // as `T`. The input and output lifetimes are the same, so mutable
        // aliasing rules will be upheld. Finally, because the inner `T` is the
        // final element of `Strategy`, the pointer metadata of the two pointers
        // will be the same.
        unsafe { core::mem::transmute::<&mut T, &mut Self>(inner) }
    }
}

impl<T, E> Deref for Strategy<T, E> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T, E> DerefMut for Strategy<T, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

/// Helper methods for `Context`s.
pub trait Trace {
    /// Wraps the error value of this type with additional context.
    fn trace<R>(self, trace: R) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static;

    /// Wraps the error value of this type with additional context. The
    /// additional context is evaluated only if an error occurred.
    fn with_trace<R, F>(self, f: F) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static,
        F: FnOnce() -> R;
}

impl<T, E> Trace for Result<T, E>
where
    E: Traceable,
{
    fn trace<R>(self, trace: R) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static,
    {
        match self {
            x @ Ok(_) => x,
            Err(e) => Err(e.add_trace(trace)),
        }
    }

    fn with_trace<R, F>(self, f: F) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static,
        F: FnOnce() -> R,
    {
        match self {
            x @ Ok(_) => x,
            Err(e) => Err(e.add_trace(f())),
        }
    }
}

pub use core::convert::Infallible;

impl Traceable for Infallible {
    fn add_trace<R>(self, _: R) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static,
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

impl Traceable for Panic {
    fn add_trace<R>(self, _: R) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static,
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

impl Traceable for Failure {
    fn add_trace<R>(self, _: R) -> Self
    where
        R: fmt::Debug + fmt::Display + Send + Sync + 'static,
    {
        self
    }
}

impl Error for Failure {
    fn new<T: StdError + Send + Sync + 'static>(_: T) -> Self {
        Self
    }
}

#[cfg(feature = "alloc")]
pub use boxed_error::BoxedError;
