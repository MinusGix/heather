//! A module pass's part of the elaborator: entering a module and elaborating its items in order.

use crate::Elaborator;

/// A module pass's part of the elaborator: entering a module and elaborating its items in order.
pub(crate) struct ModulePassMut<'e>(pub(crate) &'e mut Elaborator);

impl std::ops::Deref for ModulePassMut<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl std::ops::DerefMut for ModulePassMut<'_> {
    fn deref_mut(&mut self) -> &mut Elaborator {
        self.0
    }
}
