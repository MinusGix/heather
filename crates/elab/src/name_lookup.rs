//! Name lookup's part of the elaborator: resolving a written name and reading the world's globals.

use crate::Elaborator;

/// Name lookup's part of the elaborator: resolving a written name and reading the world's globals.
pub(crate) struct NameLookup<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for NameLookup<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}
