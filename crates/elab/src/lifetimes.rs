//! The [`Elaborator`]'s fields, grouped by how long they live.
//!
//! An elaborator is a long-lived session, but its state does not all live as
//! long as the session. Read by lifetime it falls into six classes
//! (`docs/implicit-state-machines-survey.md` §1), and each class has exactly
//! one rule for what a clone gets and one for what a rollback does:
//!
//! | Group | Clone | Rollback | Probe ([`Elaborator::probe`]) |
//! |-------|-------|----------|-------|
//! | [`CommittedWorld`] (`committed`) | shared, copy on write | `SessionCheckpoint::restore` | untouched: no cell, and a probe holds `&self` |
//! | [`ModulePass`] (`pass`) | field by field, in [`ModulePass`]'s own `Clone` | [`ModulePass::roll_back_to`], field by field | [`ModulePass::probe_mark`]: logs cut back, field by field |
//! | `DeclAttempt` (`attempt`) | deep copy | `DeclAttempt::{prepare, finish}` | `DeclAttempt::{mark, restore}`: logs cut back, cells restored, field by field |
//! | [`DynamicScope`] (`scope`) | copied: a clone inherits the extent it was taken in | the snapshot's; a site restores the *outer* value with [`Elaborator::scoped`] | [`DynamicScope::cells`]: every cell put back |
//! | [`Policy`] (`policy`) | copied, collectors shared | the snapshot's (a declaration never changes it) | untouched (only `&mut` changes it) |
//! | [`Memos`] (`memos`) | copied | the snapshot's; [`Memos::clear_positional`] on every Ψ rollback | kept: a function of committed state, which a probe cannot change |
//!
//! A *probe* is speculative elaboration through `&self` whose effects are all
//! discarded: does this operand infer, what type does it have. It used to run
//! on `self.clone()`, which deep-copied the attempt's logs — a fifth of cold
//! elaboration on operator-heavy files
//! (`issues/elab-probe-clone-copies-attempt.md`). Since a probe holds only
//! `&self`, everything it can change sits behind a cell, so it runs in place
//! and is then cut back: O(fields), not O(what the attempt has recorded).
//! The probe column is that rule per group; the groups' `mark`s destructure
//! every field, so a new cell has to pick it.
//!
//! [`Elaborator::restore_from_clone`] is "restore every group but the module
//! pass, and let the module pass decide field by field", and it destructures
//! the snapshot, so a new top-level field does not compile until it has said
//! which. A new field *inside* a group gets that group's rules; `ModulePass`'s
//! `Clone` and `roll_back_to` and `Memos::clear_positional` each name every
//! field of their group, so a field added there does not compile until it has
//! picked its rule either. That was the hole the deferred kernel gate fell
//! into once: a whole-elaborator undo (`*self = snapshot`) assigned a clone's
//! inline, empty pool over the live one and silently dropped the module's
//! queued verdicts (`pool.rs`, `KernelPool`'s `Drop`).

use super::*;

/// One queued derivation: goal, level, carrier head, and an open
/// derivation's value (see [`ModulePass::pending_derived`]). The goal names
/// committed definitions only, so it needs no record of the Ψ it was
/// captured in.
pub(crate) type PendingDerived = (Type, Level, Option<String>, Option<Term>);

/// State one *module pass* owns: what the deferred kernel gate has in flight,
/// the item loop's position, and the diagnostics and reports the pass has
/// accumulated (`docs/parallel-kernel-gate-design.md` §5).
///
/// A declaration rollback ([`Elaborator::restore_from_clone`]) never takes
/// the pool or the replay cursor back from its snapshot, and takes the
/// journal back only as far as the snapshot's lengths; the rest it takes from
/// the snapshot. The wider rollback, of a whole discarded pass, is
/// `restore_module_pass` (`session.rs`).
pub(crate) struct ModulePass {
    /// The deferred kernel gate's worker pool
    /// (`docs/parallel-kernel-gate-design.md`). One worker — the default — is
    /// exactly today's serial behaviour, spawns no thread, and queues nothing.
    /// Not shared by clones: a clone gets a fresh pool with the same worker
    /// count, like the rest of the transient scratch state.
    pub(crate) kernel_pool: pool::KernelPool,
    /// The verdicts a discarded parallel pass earned, held for the serial
    /// replay that follows it (`docs/parallel-kernel-gate-design.md` §5.2).
    /// Empty everywhere else, and never inherited by a clone.
    pub(crate) kernel_replay: pool::ReplaySlot,
    /// Logical semantic additions made while one module delta is extracted.
    /// Failed transactions truncate this alongside committed state.
    pub(crate) module_journal: module_delta::JournalSlot,
    /// The previous delta a module pass may replay slices from
    /// (`check_module_delta_from`); `None` on every other pass.
    pub(crate) slice_plan: Option<module_delta::SlicePlan>,
    /// The names the container being elaborated declares, and whether each
    /// carries `decreases` — what `docs/mutual-recursion-design.md` §8's
    /// sentence on an unbound forward reference needs. Full declared names:
    /// a member `V::get` further down does not make a bare `get` "declared
    /// below", since a member's base name is never ambient
    /// (docs/receiver-member-resolution-design.md §3).
    pub(crate) container_decls: RefCell<Vec<(String, bool, usize)>>,
    /// How far the container's item loop has got — only a declaration still
    /// *ahead* of it is the forward reference §8 explains.
    pub(crate) container_at: Cell<usize>,
    /// Non-fatal diagnostics raised so far, in the order they were raised
    /// (`docs/diagnostic-warnings-design.md` §3). A `RefCell` because the
    /// places that raise one hold `&self` — the pattern compiler is the first
    /// customer and takes `&self` throughout, exactly as `goals` and
    /// `pending_derived` do.
    ///
    /// Drained by [`Elaborator::take_warnings`](crate::Elaborator::take_warnings), never by the elaborator: a warning
    /// belongs to whoever has the source text to render it against, and that
    /// is the caller (§3).
    pub(crate) warnings: RefCell<Vec<Warning>>,
    /// Successful Omega reconstruction steps, including recursively generated
    /// logical branches, in checking order.
    pub(crate) omega_reports: RefCell<Vec<OmegaReport>>,
    /// Exhausted Omega searches. Unlike successful certificate reports these
    /// are diagnostic history, so declaration rollback deliberately retains
    /// them for the caller that receives the corresponding error.
    pub(crate) omega_failure_reports: RefCell<Vec<OmegaReport>>,
    /// Goals this item's elaboration derived and that deserve a canonical
    /// global. Ψ must not grow mid-declaration, so minting is a **restart**:
    /// the item is rolled back, the queue drained, the item elaborated again
    /// (§8). Empty for every program that resolves nothing, which is what
    /// keeps the whole mechanism free.
    ///
    /// The last slot is an **open** derivation's value
    /// ([`Resolution::record_open`](crate::resolve::Resolution::record_open)): the type is then a Π over the context
    /// prefix the answer lived in, and the mint abstracts this term over the
    /// same binders instead of re-running the search.
    pub(crate) pending_derived: RefCell<Vec<PendingDerived>>,
    /// `f_unfold` names the `decreases` walk declined to generate, and why
    /// (`docs/decreases-unfolding-design.md` §3): a reference to one reports
    /// the body shape that stopped the walk rather than an unknown name.
    pub(crate) unfold_refusals: RefCell<std::collections::HashMap<String, String>>,
    /// Every theorem's proof, by absolute Ψ index, when an exporter asked
    /// for them ([`Elaborator::keep_proofs_for_export`](crate::Elaborator::keep_proofs_for_export)); `None` otherwise. Kept
    /// beside Ψ and never sealed: sealing would let conversion unseal the
    /// proof at a stuck elimination and could change verdicts, while export
    /// only reads it (`issues/export-keeps-proofs.md`). Each entry carries
    /// its statement, so an entry left behind by a rolled-back declaration
    /// never answers for the binding that later reuses its index.
    pub(crate) export_proofs: Option<std::collections::BTreeMap<usize, (Rc<Type>, Rc<Term>)>>,
}

impl ModulePass {
    pub(crate) fn new() -> Self {
        ModulePass {
            kernel_pool: pool::KernelPool::default(),
            kernel_replay: pool::ReplaySlot::default(),
            module_journal: module_delta::JournalSlot::new(),
            slice_plan: None,
            container_decls: RefCell::new(Vec::new()),
            container_at: Cell::new(0),
            warnings: RefCell::new(Vec::new()),
            omega_reports: RefCell::new(Vec::new()),
            omega_failure_reports: RefCell::new(Vec::new()),
            pending_derived: RefCell::new(Vec::new()),
            unfold_refusals: RefCell::new(std::collections::HashMap::new()),
            export_proofs: None,
        }
    }

    /// Roll this pass back to `snapshot`, a clone of it taken earlier — the
    /// module-pass half of [`Elaborator::restore_from_clone`].
    ///
    /// **The pool stays live.** Its queue holds the *module's* outstanding
    /// proof obligations, not the rolled-back declaration's, and a clone's
    /// pool is inline and empty by construction: taking it would drop every
    /// queued verdict and leave the gate inline for the rest of the module
    /// (the defect `KernelPool`'s `Drop` now catches).
    ///
    /// **So does the replay cursor**, for the same reason: it counts the gate
    /// sites this pass has reached, and a clone's is empty. Taking it would
    /// rewind the cursor to a declaration the replay has already passed, which
    /// costs the rest of the module's reuse (never a wrong verdict — a
    /// rewound cursor mismatches and stops — but the same silent,
    /// load-dependent shape).
    ///
    /// **The journal is cut back** to the lengths the snapshot recorded
    /// (`module_delta::JournalSlot`). Everything else is the snapshot's.
    pub(crate) fn roll_back_to(&mut self, snapshot: ModulePass) {
        let ModulePass {
            kernel_pool: _,
            kernel_replay: _,
            module_journal,
            slice_plan,
            container_decls,
            container_at,
            warnings,
            omega_reports,
            omega_failure_reports,
            pending_derived,
            unfold_refusals,
            export_proofs,
        } = snapshot;
        let live = self.module_journal.take();
        self.module_journal = module_journal;
        self.module_journal.restore(live);
        self.slice_plan = slice_plan;
        self.container_decls = container_decls;
        self.container_at = container_at;
        self.warnings = warnings;
        self.omega_reports = omega_reports;
        self.omega_failure_reports = omega_failure_reports;
        self.pending_derived = pending_derived;
        self.unfold_refusals = unfold_refusals;
        self.export_proofs = export_proofs;
    }
}

/// Where a probe started in the module pass: the lengths of the logs a
/// `&self` path appends to ([`ModulePass::probe_mark`]).
pub(crate) struct PassMark {
    warnings: usize,
    omega_reports: usize,
    omega_failure_reports: usize,
    pending_derived: usize,
    journal: Option<(usize, usize)>,
}

impl ModulePass {
    /// Mark the pass for a probe. Spelled field by field: a probe holds
    /// `&self`, so only a cell can change, and each cell either is a log cut
    /// back by [`Self::probe_restore`] or is written only on `&mut` paths.
    pub(crate) fn probe_mark(&self) -> PassMark {
        let ModulePass {
            // `submit` and `join` take `&mut`.
            kernel_pool: _,
            // Consulted only at the gate sites, which take `&mut`.
            kernel_replay: _,
            module_journal,
            // A plain field.
            slice_plan: _,
            // The item loop's, set on `&mut` paths.
            container_decls: _,
            container_at: _,
            warnings,
            omega_reports,
            omega_failure_reports,
            pending_derived,
            // Written by the `decreases` walk, on `&mut` paths.
            unfold_refusals: _,
            // A plain field.
            export_proofs: _,
        } = self;
        PassMark {
            warnings: warnings.borrow().len(),
            omega_reports: omega_reports.borrow().len(),
            omega_failure_reports: omega_failure_reports.borrow().len(),
            pending_derived: pending_derived.borrow().len(),
            journal: module_journal.borrow().as_ref().map(|j| (j.events.len(), j.items.len())),
        }
    }

    /// Cut the pass's logs back to `mark`. A clone probe dropped all of
    /// these with the clone, the omega failure reports included (a
    /// declaration rollback keeps those; a probe's search is nobody's
    /// diagnostic).
    pub(crate) fn probe_restore(&self, mark: PassMark) {
        self.warnings.borrow_mut().truncate(mark.warnings);
        self.omega_reports.borrow_mut().truncate(mark.omega_reports);
        self.omega_failure_reports.borrow_mut().truncate(mark.omega_failure_reports);
        self.pending_derived.borrow_mut().truncate(mark.pending_derived);
        if let (Some((events, items)), Some(journal)) = (mark.journal, self.module_journal.borrow_mut().as_mut()) {
            journal.events.truncate(events);
            journal.items.truncate(items);
        }
    }
}

/// What a clone of a module pass gets. Spelled field by field so that a new
/// field has to choose.
impl Clone for ModulePass {
    fn clone(&self) -> Self {
        ModulePass {
            // A fresh inline pool, one worker. A clone is a speculative or
            // scoped elaborator (a candidate, a probe, a generated item), and
            // spawning and tearing down a pool per candidate would cost more
            // than the handful of declarations inside one could save. A
            // driver that wants a clone to run wide says so with
            // `set_kernel_workers` (`Elaborator::fork` does).
            kernel_pool: pool::KernelPool::inline(),
            // Never inherited: the verdicts belong to the pass replaying them.
            kernel_replay: pool::ReplaySlot::default(),
            // Only the journal's lengths, which are what a rollback to this
            // clone cuts the live journal back to.
            module_journal: self.module_journal.lengths_only(),
            slice_plan: self.slice_plan.clone(),
            container_decls: self.container_decls.clone(),
            container_at: self.container_at.clone(),
            warnings: self.warnings.clone(),
            omega_reports: self.omega_reports.clone(),
            omega_failure_reports: self.omega_failure_reports.clone(),
            pending_derived: self.pending_derived.clone(),
            unfold_refusals: self.unfold_refusals.clone(),
            export_proofs: self.export_proofs.clone(),
        }
    }
}

/// Fields set for a dynamic extent — a declaration, an instance block, a
/// tactic's run, a quotation payload, one search candidate — and put back
/// when it ends. Outside every extent each holds its inert value (`None`,
/// empty, zero).
///
/// A clone inherits the extent it was taken in (deliberately so for
/// `expr_depth`: speculative elaboration must not start a fresh native-stack
/// budget). A site that enters an extent should do it through
/// [`Elaborator::scoped`] or [`Elaborator::scoped_cell`], which restore the
/// *outer* value rather than resetting to the inert one, so that an extent
/// that nests is right by default (`docs/implicit-state-machines-survey.md`
/// §8). The depth counters keep their own guards (`ExprDepthGuard`,
/// `omega_cert::CertificateScope`, `ring.rs`'s `Depth`, `ResolutionScope`).
#[derive(Clone, Default)]
pub(crate) struct DynamicScope {
    /// The owner of the declaration being elaborated (`List` while checking
    /// `List::append`), whose other members a bare name may name
    /// ([`NameLookup::owner_member`](crate::name_lookup::NameLookup::owner_member)).
    pub(crate) member_owner: Option<String>,
    /// The declaration being elaborated, if its recursion plan is
    /// [`recursion::RecursionPlan::Misplaced`]: its recursion name, the
    /// parameter, and the refusal a self-call lowered on it raises
    /// (issues/fn-recursion-means-the-function.md). `None` everywhere else.
    pub(crate) misplaced_recursion: RefCell<Option<(String, usize, String)>>,
    /// While a declaration is lowered by recursion at the top
    /// (docs/recursion-at-the-top-design.md §3, slice 1): the parameter it
    /// recurses on and the span of the `match` on it that
    /// [`Declarations::recursion_at_top_body`](crate::declarations::Declarations::recursion_at_top_body) wrapped the body in. That
    /// `match` is the guard, and a `Nat` `match` on a constructor term
    /// inside it takes its arm. The flag: every other explicit parameter is
    /// generalized (a fallback attempt), or only those the calls vary (the
    /// default). `None` everywhere else.
    pub(crate) recursion_at_top: Option<(usize, Span, bool)>,
    /// The written declaration a recursion at the top lowers, recorded as
    /// its surface in place of the wrapped body: readers of the surface
    /// (`reprgen`, the representation obligations) read the writer's
    /// arms, not the wrapper's. `None` everywhere else.
    pub(crate) recursion_at_top_surface: Option<std::rc::Rc<heather_syntax::Decl>>,
    /// While an `instance` block is being elaborated: the members that have
    /// already landed, as (written name, full name). An unqualified reference
    /// to one of them resolves to its global, which is the whole of "later
    /// members use earlier members by name" (docs/traits-layer1-design.md
    /// §4.2). Empty outside a block, which makes the mechanism inert.
    pub(crate) instance_scope: Vec<(String, String)>,
    /// The interface definitions (global keys) the declaration being
    /// elaborated names in its `unfolding` clause: released from the
    /// withheld set for its extent (`interfaces.rs`). Empty elsewhere.
    pub(crate) unfolded: Vec<String>,
    /// Set while a `:= derive()` route elaborates the transfer generator's
    /// emission, so that the `impl` block *inside* that emission records
    /// `Derived` rather than what its own clauses look like. `None` everywhere
    /// else, which makes the mechanism inert.
    pub(crate) impl_provenance: Option<datarepr::Provenance>,
    /// Dynamically installed scope while stored surface syntax is re-lowered.
    /// This is execution state, not a committed name-registry fact, so it must
    /// remain private to one elaborator when semantic state is shared.
    pub(crate) resolution_scopes: RefCell<Vec<Rc<names::Scope>>>,
    /// Nesting depth of generated-source elaboration. This is execution mode,
    /// not representation registry state; zero means user source. A `Cell`
    /// because the Omega certificate route raises it from a `&self` checking
    /// position.
    pub(crate) generated_depth: Cell<usize>,
    /// Quotation payloads currently elaborating (`quote.rs`), read through
    /// [`Elaborator::under_quotation`]. The checked spellings of
    /// `docs/intro-by-type-design.md` §2.3 may not appear inside a `box`: the
    /// code grammar, `code_eq` and the 60 recursor branches range over that
    /// payload, and `tm_pair`'s branch telescope types its field
    /// sub-structures by `U_S`/`U_T`, which a collapsed annotation cannot
    /// state (§2.2). The design spelled this restriction as "layers p and m",
    /// which does not transcribe: Heather checks **every** declaration body at
    /// `Layer::Code` (`DESIGN.md`'s δ-layer-preservation argument is why), so
    /// a layer predicate is constantly false. "Under a quotation" is the
    /// property §2.2 actually needs.
    ///
    /// The one home of that bit. It used to be held twice, here and as a
    /// `Cx::quoted` flag on the payload's context, because a helper inside a
    /// payload that starts from a fresh `Cx` lost the flag; a dynamic extent
    /// is exactly what this group is for, so the flag went
    /// (`docs/implicit-state-machines-survey.md` §7).
    pub(crate) quote_depth: Cell<u32>,
    /// The Ψ-extending binders of the `meta fn` currently elaborating (its
    /// `Ctx`/`TyCode` binders, plus letbox-bound code globals during quote
    /// assembly). The whnf/conv oracles append these to Ψ so meta-bound
    /// `GlobalVar`s resolve to the right bindings — the goal machinery's
    /// padding trick, one layer up. Empty outside a `meta fn`.
    pub(crate) meta_pushed: RefCell<Vec<GlobalBinding>>,
    /// Active checking/inference frames. Clones inherit the current depth so
    /// speculative elaboration cannot start a fresh native-stack budget.
    pub(crate) expr_depth: Cell<usize>,
    /// Backchaining depth, for the recursion cap. A `Cell` because resolution
    /// recurses *through* `elab_check` — the nested obligation is discovered
    /// by `apply_implicit`, not passed down.
    pub(crate) resolve_depth: Cell<usize>,
    /// The `positivity` tactic in progress, if any: while it is `Some`, a
    /// proposition goal the evidence rules cannot close falls back to
    /// `omega` ([`resolve::PositivityRun`]). `None` everywhere else, so plain
    /// `:= infer` never runs omega.
    pub(crate) positivity: RefCell<Option<resolve::PositivityRun>>,
    /// The evidence rule a search is citing right now (`resolve.rs`,
    /// `build_candidate`). Its qualified name resolves when the rule's module
    /// is in the import closure of the module being elaborated (imported, or
    /// imported by an import: `field_division`'s clients reach
    /// `ordered_sign`'s sign rules through it), even inside a default that
    /// runs in another declaring scope: `Rat(1, F.top())` in a float module runs
    /// `Rat`'s `den_pos` default in `rat`'s scope, which does not import
    /// `float`, yet the rule about `F.top()` is the caller's to use.
    pub(crate) rule_citation: RefCell<Option<String>>,
    /// Set while a `by`'s tactic expression is elaborated: terms of the
    /// goal's context are quoted where it expects a `tactic::Expr`
    /// (`host::Quoting`).
    pub(crate) by_quoting: RefCell<Option<Rc<host::Quoting>>>,
    /// Set while a tactic's split is elaborated: what its branch leaves
    /// record or are filled with (`host::Leaves`).
    pub(crate) host_leaves: RefCell<Option<Rc<RefCell<host::Leaves>>>>,
    /// How many `omega` certificates are currently being checked above this
    /// point: the nesting depth recorded in [`OmegaPhases`].
    pub(crate) omega_depth: Cell<usize>,
    /// The facts each Bool-guard round being checked above this point has
    /// read (`omega_cert::split_bool_guards`), one entry per round: the
    /// omegas inside a round do not read them again.
    pub(crate) omega_settled_guards: RefCell<Vec<Vec<String>>>,
    /// How many `ring` certificates are being checked above this point
    /// (`ring.rs`): their library names resolve as `omega`'s do.
    pub(crate) ring_depth: Cell<usize>,
    /// The span of the method call `\0mutated(x.m(a))` or `\0mutcall(…)`
    /// that `statements::elaborate_mut_call` is inferring: there a dot call
    /// may resolve to a `mut self` method, since the statement threads its
    /// receiver. A dot call of one anywhere else is refused
    /// ([`Members::refuse_unthreaded_mut_call`](crate::dispatch::Members::refuse_unthreaded_mut_call),
    /// docs/effects-capabilities-design.md §2.2). `None` everywhere else.
    pub(crate) mut_call_site: Cell<Option<Span>>,
}

/// The values of [`DynamicScope`]'s cells, for a probe to put back
/// ([`DynamicScope::cells`]). The plain fields need nothing: a probe holds
/// `&self`.
pub(crate) struct ScopeCells {
    misplaced_recursion: Option<(String, usize, String)>,
    resolution_scopes: Vec<Rc<names::Scope>>,
    generated_depth: usize,
    quote_depth: u32,
    meta_pushed: Vec<GlobalBinding>,
    expr_depth: usize,
    resolve_depth: usize,
    positivity: Option<resolve::PositivityRun>,
    rule_citation: Option<String>,
    by_quoting: Option<Rc<host::Quoting>>,
    host_leaves: Option<Rc<RefCell<host::Leaves>>>,
    omega_depth: usize,
    omega_settled_guards: Vec<Vec<String>>,
    ring_depth: usize,
    mut_call_site: Option<Span>,
}

impl DynamicScope {
    /// Every cell's value, for [`Self::put_cells`]. Each is set for an
    /// extent and put back when it ends, so a probe that returns normally
    /// leaves them as it found them; this is for the paths that do not (an
    /// early `?` between a `set` and its reset), which a clone used to
    /// swallow. The vectors are stacks a few entries deep.
    pub(crate) fn cells(&self) -> ScopeCells {
        let DynamicScope {
            member_owner: _,
            misplaced_recursion,
            recursion_at_top: _,
            recursion_at_top_surface: _,
            instance_scope: _,
            unfolded: _,
            impl_provenance: _,
            resolution_scopes,
            generated_depth,
            quote_depth,
            meta_pushed,
            expr_depth,
            resolve_depth,
            positivity,
            rule_citation,
            by_quoting,
            host_leaves,
            omega_depth,
            omega_settled_guards,
            ring_depth,
            mut_call_site,
        } = self;
        ScopeCells {
            misplaced_recursion: misplaced_recursion.borrow().clone(),
            resolution_scopes: resolution_scopes.borrow().clone(),
            generated_depth: generated_depth.get(),
            quote_depth: quote_depth.get(),
            meta_pushed: meta_pushed.borrow().clone(),
            expr_depth: expr_depth.get(),
            resolve_depth: resolve_depth.get(),
            positivity: positivity.borrow().clone(),
            rule_citation: rule_citation.borrow().clone(),
            by_quoting: by_quoting.borrow().clone(),
            host_leaves: host_leaves.borrow().clone(),
            omega_depth: omega_depth.get(),
            omega_settled_guards: omega_settled_guards.borrow().clone(),
            ring_depth: ring_depth.get(),
            mut_call_site: mut_call_site.get(),
        }
    }

    pub(crate) fn put_cells(&self, cells: ScopeCells) {
        *self.misplaced_recursion.borrow_mut() = cells.misplaced_recursion;
        *self.resolution_scopes.borrow_mut() = cells.resolution_scopes;
        self.generated_depth.set(cells.generated_depth);
        self.quote_depth.set(cells.quote_depth);
        *self.meta_pushed.borrow_mut() = cells.meta_pushed;
        self.expr_depth.set(cells.expr_depth);
        self.resolve_depth.set(cells.resolve_depth);
        *self.positivity.borrow_mut() = cells.positivity;
        *self.rule_citation.borrow_mut() = cells.rule_citation;
        *self.by_quoting.borrow_mut() = cells.by_quoting;
        *self.host_leaves.borrow_mut() = cells.host_leaves;
        self.omega_depth.set(cells.omega_depth);
        *self.omega_settled_guards.borrow_mut() = cells.omega_settled_guards;
        self.ring_depth.set(cells.ring_depth);
        self.mut_call_site.set(cells.mut_call_site);
    }
}

/// Configuration a driver sets once, before or between modules: the gate
/// oracle, the fuel, the lint profile, opt-in collectors. A declaration
/// never changes it, so a rollback has nothing to undo; collectors are
/// `Rc`s, so a clone contributes to the same measurement.
#[derive(Clone)]
pub(crate) struct Policy {
    /// The oracle consulted at the kernel gate (`gate.rs`), if any. `None` —
    /// the default, and what every test and the unflagged CLI use — means the
    /// kernel runs on every declaration, exactly as it always has.
    pub(crate) gate: Option<Arc<dyn gate::KernelGate>>,
    pub(crate) fuel: u64,
    /// Project-local style policy for written-source lints. General lints run
    /// under every profile; the CLI selects `Stdlib` only for `lib/std`.
    pub(crate) lint_profile: LintProfile,
    /// Review-mode lints run only when a driver asks (`heather check
    /// --review`): the ones whose recognizer is a second elaboration of the
    /// item, which is a cost no ordinary check should pay to say nothing
    /// (`issues/lint-redundant-match-motive.md`, 2026-09-17).
    pub(crate) review_lints: bool,
    /// Every structurally recursive `fn` is checked to unfold to its source,
    /// and refused where it does not (`meaning.rs`,
    /// issues/recursion-meaning-check.md). Off by default until its cost
    /// comes down (it re-gates every recursive body; the tactic library's
    /// `let v <- …; match v` bodies pay most, issues/tier2-type-code-functions.md);
    /// `heather check --meaning-check` sets it ([`Elaborator::set_meaning_check`]).
    pub(crate) meaning_check: bool,
    /// Tactics implemented in Rust, available as `by name`
    /// ([`Elaborator::register_native_tactic`], docs/host-elaboration-interface-design.md §8a).
    pub(crate) native_tactics: RefCell<HashMap<String, fn() -> Box<dyn host::NativeTactic>>>,
    /// Optional explicit collector for evaluator-region activity. Clones
    /// share it so speculative and generated checking contribute to the same
    /// requested measurement; ordinary elaborators leave it absent.
    pub(crate) value_metrics: Option<Rc<ValueMetrics>>,
    /// Optional emission-slot audit (`emission_walk`). Off by default and
    /// shared by clones, exactly like the two collectors above: ordinary
    /// elaboration pays one `Option` branch per declaration.
    pub(crate) emission_findings: Option<Rc<RefCell<Vec<EmissionFinding>>>>,
    /// Test-time only: inferred arguments owe no check note
    /// ([`Elaborator::forget_owed_argument_checks`](crate::Elaborator::forget_owed_argument_checks)).
    pub(crate) owed_checks_forgotten: bool,
    /// Test-time only: the structural recursion planner (`recursion::plan`)
    /// is not consulted, so a `fn` it would refuse or lower by measure is
    /// lowered structurally — the miscompiles the meaning check exists to
    /// catch ([`Elaborator::skip_recursion_plan`]).
    pub(crate) recursion_plan_skipped: bool,
}

impl Policy {
    pub(crate) fn new() -> Self {
        Policy {
            gate: None,
            fuel: DEFAULT_FUEL,
            lint_profile: LintProfile::Default,
            review_lints: false,
            meaning_check: false,
            native_tactics: RefCell::new(HashMap::new()),
            value_metrics: None,
            emission_findings: None,
            owed_checks_forgotten: false,
            recursion_plan_skipped: false,
        }
    }
}

/// Caches whose answers are a function of committed state. **Nothing here is
/// semantic**: dropping any of them changes only how long elaboration takes.
///
/// Two are keyed by absolute Ψ position, and a rollback may reuse a position
/// for a different declaration, so every Ψ rollback calls
/// [`Memos::clear_positional`]. The rest validate a hit by `Rc` identity or by
/// the Ψ length it was computed at, and survive.
#[derive(Clone, Default)]
pub(crate) struct Memos {
    /// Memo for the telescope walk in
    /// [`Callables::call_defers_for_result_only`](crate::application::Callables::call_defers_for_result_only), keyed by the global's absolute
    /// Ψ position. That test is asked at **every explicit argument of every
    /// call**, and its answer depends only on the callee's declared type,
    /// which never changes once the global is committed — so it is computed
    /// once per declaration rather than once per argument. Nothing here is
    /// semantic: dropping the memo changes only how long elaboration takes.
    pub(crate) result_only_memo: RefCell<HashMap<u32, bool>>,
    /// Bare named types from finished modules, lowered once
    /// ([`Inductives::lower_named`](crate::inductive::Inductives::lower_named)); keyed by the declaration's address and
    /// whether names are read as generated, holding the Ψ length the type
    /// was lowered at (a hit is weakened past the globals committed since).
    /// Nothing here is semantic.
    pub(crate) named_type_memo: RefCell<HashMap<(usize, bool), (Rc<Inductive>, usize, (Type, Level))>>,
    /// The last shape and index type an `IWf` family's signature was built
    /// with, by tag ([`IwfFamily::share_iwf_part`](crate::iwf_family::IwfFamily::share_iwf_part)), so equal ones are one
    /// allocation. Nothing here is semantic.
    pub(crate) iwf_part_memo: RefCell<HashMap<(u32, bool), Rc<Type>>>,
    /// The type names the program has written (`u8`, `i(n)`, its own `def
    /// Byte: Type = …`), least recently written first, each with the
    /// instance it expands to ([`Elaborator::record_type_name`]). Read only
    /// by the display, which respells an instance by the name
    /// (issues/type-name-display-respelling.md). Nothing here is semantic.
    pub(crate) type_names: RefCell<Vec<display::TypeName>>,
    /// A tactic's reading of a class carrier, by the scope it was read in
    /// ([`Resolution::scope_memo`](crate::resolve::Resolution::scope_memo)): `linarith`'s ordered field and `ring`'s
    /// ring, each elaborated from generated source, which a run reads at
    /// every fact and every `ring` step it checks. Keyed by the Ψ length, the
    /// goal padding, Γ and the carrier, and by the very `let` and dictionary
    /// spines in scope, which can bring another dictionary for the same
    /// carrier. Nothing here is semantic.
    pub(crate) scope_memo: RefCell<Vec<ScopeMemo>>,
}

/// One [`Memos::scope_memo`] entry.
#[derive(Clone)]
pub(crate) struct ScopeMemo {
    pub(crate) which: &'static str,
    pub(crate) psi: u32,
    pub(crate) pad: u32,
    pub(crate) gamma: LocalCtx,
    pub(crate) aliases: crate::spine::Spine<Rc<Alias>>,
    pub(crate) dicts: crate::spine::Spine<Rc<crate::context::DictBinder>>,
    pub(crate) carrier: Type,
    pub(crate) value: Arc<dyn std::any::Any + Send + Sync>,
}

impl Memos {
    /// Drop every answer keyed by an absolute Ψ position: called by each
    /// rollback that can move Ψ back (`SessionCheckpoint::restore`, the
    /// slice replay's), so a cached answer for a removed declaration never
    /// becomes the answer for its replacement at the same index. Names every
    /// field, so a new memo has to say whether it is positional.
    pub(crate) fn clear_positional(&self) {
        let Memos {
            result_only_memo,
            named_type_memo,
            // Keyed by tag and by an `Rc`'s address (held), not by position.
            iwf_part_memo: _,
            // Holds the Ψ position of each name's definition: a rollback can
            // put another `def` of the same name there.
            type_names,
            // Keyed by the Ψ length, but a rollback can rebuild Ψ to the
            // same length with other declarations.
            scope_memo,
        } = self;
        scope_memo.borrow_mut().clear();
        result_only_memo.borrow_mut().clear();
        named_type_memo.borrow_mut().clear();
        type_names.borrow_mut().clear();
    }
}

/// A [`DynamicScope`] field's cell, for [`Elaborator::scoped_cell`].
pub(crate) trait ScopeCell {
    type Value;
    /// Store `value`, handing back what was there.
    fn put(&self, value: Self::Value) -> Self::Value;
}

impl<T> ScopeCell for Cell<T> {
    type Value = T;
    fn put(&self, value: T) -> T {
        self.replace(value)
    }
}

impl<T> ScopeCell for RefCell<T> {
    type Value = T;
    fn put(&self, value: T) -> T {
        self.replace(value)
    }
}

/// Where a probe started: one mark per group a probe can change
/// ([`Elaborator::probe`]).
struct ProbeMark {
    pass: PassMark,
    attempt: attempt::AttemptMark,
    scope: ScopeCells,
}

/// Puts the elaborator back when the probe ends, by return or by unwind.
struct ProbeGuard<'a> {
    elab: &'a Elaborator,
    mark: Option<ProbeMark>,
}

impl Drop for ProbeGuard<'_> {
    fn drop(&mut self) {
        let ProbeMark { pass, attempt, scope } = self.mark.take().expect("restored once");
        // Innermost first is all a nested probe needs, and a guard's scope
        // gives it.
        self.elab.scope.put_cells(scope);
        self.elab.attempt.restore(attempt);
        self.elab.pass.probe_restore(pass);
    }
}

impl Elaborator {
    /// Run `body` — speculative elaboration through `&self` — and then
    /// take back everything it changed: the goals it allocated or solved,
    /// the notes, dependencies and warnings it recorded, the cells it left
    /// set. What `self.clone()` and dropping the clone gave, at O(fields)
    /// instead of O(everything the attempt has recorded) (the module doc's
    /// probe column; `issues/elab-probe-clone-copies-attempt.md`).
    ///
    /// Read whatever the probe's answer depends on *inside* `body`: a type
    /// it inferred may mention a goal the restore frees. The caches in
    /// [`Memos`] keep what the probe computed, as they are not semantic.
    pub(crate) fn probe<Out>(&self, body: impl FnOnce() -> Out) -> Out {
        let _guard = ProbeGuard {
            elab: self,
            mark: Some(ProbeMark {
                pass: self.pass.probe_mark(),
                attempt: self.attempt.mark(),
                scope: self.scope.cells(),
            }),
        };
        body()
    }

    /// Run `body` with one [`DynamicScope`] field set to `value`, then put
    /// the *outer* value back, error or not (`body`'s result is bound before
    /// the restore). `field` names the field: `|s| &mut s.member_owner`.
    pub(crate) fn scoped<T, Out>(
        &mut self,
        field: fn(&mut DynamicScope) -> &mut T,
        value: T,
        body: impl FnOnce(&mut Self) -> Out,
    ) -> Out {
        let outer = std::mem::replace(field(&mut self.scope), value);
        let out = body(self);
        *field(&mut self.scope) = outer;
        out
    }

    /// The `&self` form of [`Self::scoped`], for a field behind a cell and a
    /// body that holds no exclusive borrow: `|s| &s.positivity`.
    pub(crate) fn scoped_cell<C: ScopeCell, Out>(
        &self,
        field: fn(&DynamicScope) -> &C,
        value: C::Value,
        body: impl FnOnce() -> Out,
    ) -> Out {
        let outer = field(&self.scope).put(value);
        let out = body();
        field(&self.scope).put(outer);
        out
    }
}
