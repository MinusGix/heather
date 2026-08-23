//! Atomic checkpoints for the elaborator's committed session state.
//!
//! Generated declarations are ordinary declarations: each one checks and
//! commits independently. A generator, however, emits a *bundle* whose only
//! meaningful outcomes are that every declaration lands or none do. This is
//! the one rollback boundary spanning every durable registry those ordinary
//! commits can change.

use std::collections::HashMap;

use heather_kernel::term::GlobalCtx;

use crate::{Elaborator, MetaDef, Names, Representations, Slot, Traits, Types, R};

/// A complete snapshot of facts committed by successful declarations.
///
/// Dynamic scope, diagnostics, configuration, and per-attempt scratch state
/// deliberately do not live here. Their owners already delimit their
/// lifetimes; conflating them with committed program state would make a
/// speculative rollback silently undo caller policy or diagnostic history.
struct SessionCheckpoint {
    psi: GlobalCtx,
    delta_psi: GlobalCtx,
    names: Names,
    types: Types,
    traits: Traits,
    representations: Representations,
    meta_defs: HashMap<String, MetaDef>,
    meta_slots: HashMap<Slot, (String, String)>,
}

impl SessionCheckpoint {
    fn capture(elab: &Elaborator) -> Self {
        Self {
            psi: elab.psi.clone(),
            delta_psi: elab.delta_psi.clone(),
            names: elab.names.clone(),
            types: elab.types.clone(),
            traits: elab.traits.clone(),
            representations: elab.representations.clone(),
            meta_defs: elab.meta_defs.clone(),
            meta_slots: elab.meta_slots.clone(),
        }
    }

    fn restore(self, elab: &mut Elaborator) {
        elab.psi = self.psi;
        elab.delta_psi = self.delta_psi;
        elab.names = self.names;
        elab.types = self.types;
        elab.traits = self.traits;
        elab.representations = self.representations;
        elab.meta_defs = self.meta_defs;
        elab.meta_slots = self.meta_slots;

        // Absolute Ψ positions may be reused after rollback. A cached answer
        // for a removed declaration must not become the answer for its future
        // replacement at the same index.
        elab.result_only_memo.borrow_mut().clear();
    }
}

impl Elaborator {
    /// Run an operation atomically with respect to all committed session
    /// state. The original error is returned after restoring the checkpoint.
    pub(crate) fn session_transaction<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> R<T>,
    ) -> R<T> {
        let checkpoint = SessionCheckpoint::capture(self);
        let result = operation(self);
        if result.is_err() {
            checkpoint.restore(self);
        }
        result
    }
}
