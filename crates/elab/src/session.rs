//! Atomic checkpoints for the elaborator's committed session state.
//!
//! Generated declarations are ordinary declarations: each one checks and
//! commits independently. A generator, however, emits a *bundle* whose only
//! meaningful outcomes are that every declaration lands or none do. This is
//! the one rollback boundary spanning every durable registry those ordinary
//! commits can change.

use heather_kernel::rc::Rc;

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
        elab.memos.clear_positional();
    }
}

/// Everything one *module pass* can leave behind, and the marks it rolls back
/// to.
///
/// [`SessionCheckpoint`] is the committed-state half and is deliberately
/// narrow (see its own note). A module pass, though, is the unit the deferred
/// kernel gate discards when a queued proof fails
/// (`docs/parallel-kernel-gate-design.md` §5.1), and *nothing* a discarded
/// pass did may be observable: not the bindings it registered, not the
/// warnings it raised, not the Omega certificates it reported, not the delta
/// events it journalled, not the `--timings` rows it pushed. So this is the
/// wider boundary, and it exists for exactly one caller.
pub(crate) struct ModulePassCheckpoint {
    committed: SessionCheckpoint,
    journal: Option<(usize, usize)>,
    warnings: usize,
    omega_reports: usize,
    omega_failure_reports: usize,
    rows: crate::stats::RowsMark,
}

impl Elaborator {
    /// Mark everything a module pass could change, so that a pass whose
    /// deferred proofs failed can be replayed serially from here.
    pub(crate) fn module_pass_checkpoint(&self) -> ModulePassCheckpoint {
        ModulePassCheckpoint {
            committed: SessionCheckpoint::capture(self),
            journal: self
                .pass.module_journal
                .borrow()
                .as_ref()
                .map(|journal| (journal.events.len(), journal.items.len())),
            warnings: self.pass.warnings.borrow().len(),
            omega_reports: self.pass.omega_reports.borrow().len(),
            omega_failure_reports: self.pass.omega_failure_reports.borrow().len(),
            rows: crate::stats::rows_mark(),
        }
    }

    /// Undo a module pass completely. The elaborator is left exactly as
    /// [`Self::module_pass_checkpoint`] found it, so the replay re-enters the
    /// module, re-registers its names and re-raises its diagnostics itself.
    pub(crate) fn restore_module_pass(&mut self, mark: ModulePassCheckpoint) {
        mark.committed.restore(self);
        if let Some((events, items)) = mark.journal
            && let Some(journal) = self.pass.module_journal.borrow_mut().as_mut()
        {
            journal.events.truncate(events);
            journal.items.truncate(items);
        }
        self.pass.warnings.borrow_mut().truncate(mark.warnings);
        self.pass.omega_reports.borrow_mut().truncate(mark.omega_reports);
        self.pass.omega_failure_reports
            .borrow_mut()
            .truncate(mark.omega_failure_reports);
        self.pass.pending_derived.borrow_mut().clear();
        self.pass.container_decls.borrow_mut().clear();
        self.scope.instance_scope.clear();
        crate::stats::truncate_rows(mark.rows);
    }

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

    /// An elaborator configured as this one (its gate, kernel width, lints,
    /// collectors) over `image`'s world instead of its own: where a driver
    /// elaborates a module over exactly its import closure
    /// (`docs/module-dag-design.md` §6). The memos keyed by Ψ position are
    /// dropped, as a rollback drops them, and nothing this elaborator has
    /// pending (warnings, reports, a journal) comes along.
    pub fn fork_over(&self, image: &SemanticImage) -> Elaborator {
        let mut elab = self.fork();
        image.committed.clone().restore(&mut elab);
        elab.take_warnings();
        elab.take_omega_reports();
        elab
    }

    /// Run an operation atomically with respect to all committed session
    /// state. The original error is returned after restoring the checkpoint.
    pub(crate) fn session_transaction<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> R<T>,
    ) -> R<T> {
        let checkpoint = SessionCheckpoint::capture(self);
        let journal_mark = self
            .pass.module_journal
            .borrow()
            .as_ref()
            .map(|journal| (journal.events.len(), journal.items.len()));
        let result = operation(self);
        if result.is_err() {
            checkpoint.restore(self);
            if let Some((events, items)) = journal_mark
                && let Some(journal) = self.pass.module_journal.borrow_mut().as_mut()
            {
                journal.events.truncate(events);
                journal.items.truncate(items);
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use heather_kernel::rc::Rc;

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
