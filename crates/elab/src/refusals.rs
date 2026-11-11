//! Kernel refusals' part of the elaborator: turning a refused judgment into a located error.

use crate::Elaborator;

/// Kernel refusals' part of the elaborator: turning a refused judgment into a located error.
pub(crate) struct Refusals<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Refusals<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}
