//! The notes a refused check carries: what the two sides were and where they part.

use crate::Elaborator;

/// The notes a refused check carries: what the two sides were and where they part.
pub(crate) struct MismatchNotes<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for MismatchNotes<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}
