//! Declarations' part of the elaborator: the readings a declaration's head and recursion plan need.

use crate::Elaborator;

/// Declarations' part of the elaborator: the readings a declaration's head and recursion plan need.
pub(crate) struct Declarations<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Declarations<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}
