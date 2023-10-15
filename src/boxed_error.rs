use core::fmt;

use crate::{thin_box::ThinBox, Error, StdError};

#[ptr_meta::pointee]
trait ErrorContext: fmt::Debug + fmt::Display + Send + Sync + 'static {}

impl<T> ErrorContext for T where T: fmt::Debug + fmt::Display + Send + Sync + 'static + ?Sized {}

#[derive(Debug)]
struct WithContext {
    error: BoxedError,
    context: ThinBox<dyn ErrorContext>,
}

impl fmt::Display for WithContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error)?;
        write!(f, "context: {}", self.context)?;

        Ok(())
    }
}

impl StdError for WithContext {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.error.inner.source()
    }
}

/// A thin boxed [`Error`] that fits in a single pointer.
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

impl Error for BoxedError {
    fn new<T: StdError + Send + Sync + 'static>(source: T) -> Self {
        Self {
            // SAFETY: The provided closure returns the same pointer unsized to
            // a `dyn Error`.
            inner: unsafe { ThinBox::new_unchecked(source, |ptr| ptr as *mut _) },
        }
    }

    fn context<T>(self, context: T) -> Self
    where
        T: fmt::Debug + fmt::Display + Send + Sync + 'static,
    {
        Self::new(WithContext {
            error: self,
            // SAFETY: The provided closure returns the same pointer unsized to
            // a `dyn ErrorContext`.
            context: unsafe { ThinBox::new_unchecked(context, |ptr| ptr as *mut _) },
        })
    }
}
