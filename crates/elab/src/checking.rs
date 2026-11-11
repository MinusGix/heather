//! Checking's part of the elaborator: a written expression against an expected type.

use crate::Elaborator;

/// Checking's part of the elaborator: a written expression against an expected type.
pub(crate) struct Checking<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Checking<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}
