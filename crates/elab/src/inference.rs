//! Inference's part of the elaborator: a written expression's term and type.

use crate::Elaborator;

/// Inference's part of the elaborator: a written expression's term and type.
pub(crate) struct Inference<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Inference<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}
