//! Atomic checkpoints for the elaborator's committed session state.
//!
//! Generated declarations are ordinary declarations: each one checks and
//! commits independently. A generator, however, emits a *bundle* whose only
//! meaningful outcomes are that every declaration lands or none do. This is
//! the one rollback boundary spanning every durable registry those ordinary
//! commits can change.

use std::rc::Rc;

use crate::{CommittedWorld, Elaborator, R, Shared};

/// A complete snapshot of facts committed by successful declarations.
///
/// Dynamic scope, diagnostics, configuration, and per-attempt scratch state
/// deliberately do not live here. Their owners already delimit their
/// lifetimes; conflating them with committed program state would make a
/// speculative rollback silently undo caller policy or diagnostic history.
#[derive(Clone)]
struct SessionCheckpoint {
    committed: Rc<CommittedWorld>,
}

/// An in-memory image of every semantic fact committed by an elaborator.
///
/// This is deliberately not a serialization format and not a kernel verdict:
/// it can only be obtained from an elaborator which already checked the
/// captured prefix in this process. Forking it creates fresh attempt,
/// diagnostic, report, policy, metric, memo, and gate state around the same
/// committed facts. Persistent, untrusted module images are a later stage of
/// `docs/semantic-module-images-design.md` and must recheck their decoded
/// kernel bindings before installing metadata.
#[derive(Clone)]
pub struct SemanticImage {
    committed: SessionCheckpoint,
}

impl SemanticImage {
    /// Start an isolated default-configured suffix over this committed image.
    ///
    /// The caller installs any lint profile, metrics collector, or kernel gate
    /// explicitly. In particular, a cache oracle is never inherited through
    /// an image as an accidental trust decision.
    pub fn elaborator(&self) -> Elaborator {
        let mut elab = Elaborator::new();
        self.committed.clone().restore(&mut elab);
        elab
    }
}

impl SessionCheckpoint {
    fn capture(elab: &Elaborator) -> Self {
        Self {
            committed: Rc::clone(&elab.committed),
        }
    }

    fn capture_semantic(elab: &Elaborator) -> Self {
        let mut committed = (*elab.committed).clone();
        committed.psi = Shared::new(elab.psi.semantic_snapshot());
        committed.delta_psi = Shared::new(elab.delta_psi.semantic_snapshot());
        committed.names = Shared::new(elab.names.semantic_snapshot());
        committed.types = Shared::new(elab.types.semantic_snapshot());
        committed.provenance = Shared::new(elab.provenance.semantic_snapshot());
        Self {
            committed: Rc::new(committed),
        }
    }

    fn restore(self, elab: &mut Elaborator) {
        elab.committed = self.committed;

        // Absolute Ψ positions may be reused after rollback. A cached answer
        // for a removed declaration must not become the answer for its future
        // replacement at the same index.
        elab.result_only_memo.borrow_mut().clear();
    }
}

impl Elaborator {
    /// Capture all committed semantic state and none of this session's
    /// transient checking state.
    ///
    /// The image is process-local. It is the ownership and isolation boundary
    /// from which persistent per-module images will be derived; it does not
    /// skip or stand in for a kernel judgment on disk-loaded data.
    pub fn semantic_image(&self) -> SemanticImage {
        SemanticImage {
            committed: SessionCheckpoint::capture_semantic(self),
        }
    }

    /// Run an operation atomically with respect to all committed session
    /// state. The original error is returned after restoring the checkpoint.
    pub(crate) fn session_transaction<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> R<T>,
    ) -> R<T> {
        let checkpoint = SessionCheckpoint::capture(self);
        let journal_mark = self
            .module_journal
            .borrow()
            .as_ref()
            .map(|journal| journal.events.len());
        let result = operation(self);
        if result.is_err() {
            checkpoint.restore(self);
            if let Some(mark) = journal_mark
                && let Some(journal) = self.module_journal.borrow_mut().as_mut()
            {
                journal.events.truncate(mark);
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;

    #[test]
    fn image_forks_share_then_detach_only_mutated_registries() {
        let image = Elaborator::new().semantic_image();
        let mut left = image.elaborator();
        let right = image.elaborator();

        assert!(Rc::ptr_eq(&left.committed, &right.committed));
        left.elab_source("fn id(x: Nat) -> Nat { x }").unwrap();

        assert!(!Rc::ptr_eq(&left.committed, &right.committed));
        assert!(Rc::ptr_eq(&left.types.0, &right.types.0));
        assert!(Rc::ptr_eq(&left.traits.0, &right.traits.0));
        assert!(Rc::ptr_eq(
            &left.representations.0,
            &right.representations.0,
        ));
        assert!(Rc::ptr_eq(&left.meta_programs.0, &right.meta_programs.0));
    }
}
