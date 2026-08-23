//! State whose lifetime is one ordinary declaration elaboration.

use std::cell::{Cell, RefCell};

use heather_syntax::Span;

use crate::{goals::GoalArena, OperatorFallbackUse};

/// Scratch state for an ordinary declaration.
///
/// The elaborator itself is a long-lived session. These values are not: they
/// describe one speculative declaration attempt and must be reset together on
/// retry or completion. Keeping them in one object makes that lifetime a
/// structural property instead of a cleanup convention spread across
/// `Elaborator::elab_decl`.
#[derive(Clone, Default)]
pub(super) struct DeclAttempt {
    /// Operator fallbacks taken after consulting a designation table.
    pub(super) op_fallback_notes: RefCell<Vec<String>>,
    /// Successful fallbacks which become lints only if the declaration lands.
    pub(super) op_fallback_uses: RefCell<Vec<OperatorFallbackUse>>,
    /// First checking mismatch held for a possible kernel diagnostic.
    pub(super) pending_mismatch: RefCell<Option<(String, Span)>>,

    /// Stable goal identities and their temporary Ψ prefix.
    pub(super) goal_arena: GoalArena,

    /// Slot retained during an argument-slot ownership probe.
    pub(super) slot_probe_target: Cell<Option<Span>>,
    /// Prevents nested motive-less match speculation.
    pub(super) motive_speculation: Cell<bool>,
}

impl DeclAttempt {
    /// Prepare the same state object for another attempt at the declaration.
    pub(super) fn prepare(&mut self) {
        self.op_fallback_notes.get_mut().clear();
        self.op_fallback_uses.get_mut().clear();
        self.pending_mismatch.get_mut().take();
        self.goal_arena.prepare();
    }

    /// Discard goal state produced by a speculative attempt.
    pub(super) fn clear_goals(&mut self) {
        self.goal_arena.clear();
    }

    /// Restore the declaration-independent state after success or failure.
    pub(super) fn finish(&mut self) {
        self.goal_arena.finish();
        self.op_fallback_notes.get_mut().clear();
        self.pending_mismatch.get_mut().take();
    }
}
