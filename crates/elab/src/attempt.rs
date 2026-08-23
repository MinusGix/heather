//! State whose lifetime is one ordinary declaration elaboration.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use heather_syntax::Span;

use crate::{Goal, OperatorFallbackUse};

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

    /// Total Ψ slots reserved for goals in the current attempt.
    pub(super) goal_base: u32,
    /// Syntactically written portion of `goal_base`.
    pub(super) written_goal_base: u32,
    /// Promotable implicit goals encountered in this attempt.
    pub(super) promoted_goals_seen: Cell<u32>,
    /// Goal arena in creation order.
    pub(super) goals: RefCell<Vec<Goal>>,
    /// Stable source identities for goals visited more than once.
    pub(super) goal_spans: RefCell<HashMap<(usize, usize, Option<String>), usize>>,
    /// Larger goal prefix requested by speculative application elaboration.
    pub(super) requested_goal_base: Cell<u32>,
    /// Whether capacity discovery may restart this declaration.
    pub(super) goal_restart_enabled: Cell<bool>,

    /// Slot retained during an argument-slot ownership probe.
    pub(super) slot_probe_target: Cell<Option<Span>>,
    /// True while elaborating an `on` RHS, where new holes are forbidden.
    pub(super) frozen: Cell<bool>,
    /// Prevents nested motive-less match speculation.
    pub(super) motive_speculation: Cell<bool>,
}

impl DeclAttempt {
    /// Prepare the same state object for another attempt at the declaration.
    pub(super) fn prepare(&mut self) {
        self.op_fallback_notes.get_mut().clear();
        self.op_fallback_uses.get_mut().clear();
        self.pending_mismatch.get_mut().take();
        self.requested_goal_base.set(0);
        self.promoted_goals_seen.set(0);
    }

    /// Discard goal state produced by a speculative attempt.
    pub(super) fn clear_goals(&mut self) {
        self.goals.get_mut().clear();
        self.goal_spans.get_mut().clear();
        self.frozen.set(false);
    }

    /// Restore the declaration-independent state after success or failure.
    pub(super) fn finish(&mut self) {
        self.goal_restart_enabled.set(false);
        self.goal_base = 0;
        self.written_goal_base = 0;
        self.clear_goals();
        self.op_fallback_notes.get_mut().clear();
        self.pending_mismatch.get_mut().take();
    }
}
