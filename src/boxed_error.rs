use core::fmt;

use crate::{thin_box::ThinBox, Contextual, Error, StdError};

#[ptr_meta::pointee]
trait ErrorContext: fmt::Debug + fmt::Display + Send + Sync + 'static {}

impl<T> ErrorContext for T where
    T: fmt::Debug + fmt::Display + Send + Sync + 'static + ?Sized
{
}

#[derive(Debug)]
struct ErrorWithContext {
    error: BoxedError,
    context: ThinBox<dyn ErrorContext>,
}

impl fmt::Display for ErrorWithContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error)?;
        write!(f, "context: {}", self.context)?;

        Ok(())
    }
}

impl StdError for ErrorWithContext {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.error.inner.source()
    }
}

/// An error type that preserves all detailed error messages. It is optimized
/// to fit in a single pointer.
#[derive(Debug)]
pub struct BoxedError {
    inner: ThinBox<dyn StdError + Send + Sync + 'static>,
}

impl fmt::Display for BoxedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for BoxedError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.inner.source()
    }
}

impl Contextual for BoxedError {
    fn add_context<T>(self, context: T) -> Self
    where
        T: fmt::Debug + fmt::Display + Send + Sync + 'static,
    {
        Self::new(ErrorWithContext {
            error: self,
            // SAFETY: The provided closure returns the same pointer unsized to
            // a `dyn ErrorContext`.
            context: unsafe {
                ThinBox::new_unchecked(context, |ptr| ptr as *mut _)
            },
        })
    }
}

impl Error for BoxedError {
    fn new<T: StdError + Send + Sync + 'static>(source: T) -> Self {
        Self {
            // SAFETY: The provided closure returns the same pointer unsized to
            // a `dyn Error`.
            inner: unsafe {
                ThinBox::new_unchecked(source, |ptr| ptr as *mut _)
            },
        }
    }
}
