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

/// Declarations' part of the elaborator that writes: elaborating, checking and committing one declaration.
pub(crate) struct DeclarationsMut<'e>(pub(crate) &'e mut Elaborator);

impl std::ops::Deref for DeclarationsMut<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl std::ops::DerefMut for DeclarationsMut<'_> {
    fn deref_mut(&mut self) -> &mut Elaborator {
        self.0
    }
}
