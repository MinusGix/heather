//! Application's part of the elaborator: heads, spines and solving arguments from an expected type.

use crate::Elaborator;

/// Application's part of the elaborator: heads, spines and solving arguments from an expected type.
pub(crate) struct AppUnify<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for AppUnify<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}
