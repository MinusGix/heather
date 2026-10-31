//! Logical, representation-independent semantic additions made by one module.
//!
//! This is the in-memory precursor to the persistent module-image format. It
//! records operations at infallible commit points rather than diffing private
//! maps or serializing their current storage layout.

use std::cell::RefCell;
use std::fmt;
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalCtx, SealedProof, Type};
use heather_kernel::typing::{self, TypeError};
use heather_syntax::OpFixity;

use crate::datarepr::{DatareprInfo, DatareprKey, ImplEntry, Obligation};
use crate::gendefs::{GenDef, TyCodeFn, WfSlots, SpineCodes};
use crate::inductive::Inductive;
use crate::metaprograms::MetaDef;
use crate::names::{GlobalRegistration, NameKind, Scope};
use crate::resolve::DerivedInst;
use crate::slots::Slot;
use crate::traits::{ClassInfo, DesignationInfo, EvidenceRule, InstanceInfo, InstKey};
use crate::{pool, stats, ElabError, Elaborator, R};
use crate::module_image::same_proof;

/// Ordered dependency-interface identities supplied by the module loader.
/// The digest algorithm lives outside the elaborator; these stable bytes are
/// an opaque contract. Replay additionally compares the logical kernel prefix.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModuleDependencyIdentity(Vec<[u8; 32]>);

impl ModuleDependencyIdentity {
    pub fn new(ordered_interface_hashes: Vec<[u8; 32]>) -> Self {
        Self(ordered_interface_hashes)
    }

    pub fn ordered_interface_hashes(&self) -> &[[u8; 32]] {
        &self.0
    }
}

/// A module's checked kernel suffix and logical frontend-registry additions.
/// Fields stay opaque: persistent encoding is a later layer, and replay is the
/// only operation which may install quarantined metadata.
#[derive(Clone)]
pub struct ModuleDelta {
    pub(crate) module: String,
    pub(crate) dependencies: ModuleDependencyIdentity,
    pub(crate) dependency_psi: GlobalCtx,
    pub(crate) extension: Vec<GlobalBinding>,
    /// The sealed proofs of the extension's theorems, by extension index,
    /// ascending (`issues/theorem-witness-unfolding.md`): kept beside the
    /// bindings exactly as Ψ keeps them, never in one. Part of the semantic
    /// image and not of the interface, since a dependent observes a proof
    /// only by opening it, and records that it did.
    pub(crate) sealed: Vec<(usize, Rc<SealedProof>)>,
    /// The dependency prefix's sealed proofs this module's items opened, by
    /// absolute Ψ index, as they were when they were opened. A replay over a
    /// prefix whose proof at one of these indices differs is not a replay
    /// of what was checked: the module is rebuilt (`replay_module_delta`),
    /// or only the items that opened it are (`slice_enter`).
    pub(crate) opened_dependencies: Vec<(usize, Rc<SealedProof>)>,
    pub(crate) scope: Scope,
    pub(crate) events: Vec<DeltaEvent>,
    /// One slice per item of the source file, in order: the ranges of
    /// `extension`, `events` and `warnings` that item contributed
    /// (`docs/declaration-slice-replay-design.md` §3). Empty for a delta
    /// decoded from an image until the persistent half of that design lands.
    pub(crate) items: Vec<ItemSlice>,
    /// The warnings the module raised, in order, so a replayed slice can
    /// re-raise its own. Process-local for now (not encoded).
    pub(crate) warnings: Vec<crate::diagnostics::Warning>,
    /// The module's scope right after `enter_module`, before any item: the
    /// imports the items were resolved against. A later elaboration of the
    /// same module may replay slices only from an identical entry scope.
    pub(crate) scope_at_entry: Option<Scope>,
}

/// One item's contribution to a [`ModuleDelta`], as ranges into its flat
/// vectors, keyed by the item's exact source text
/// (`docs/declaration-slice-replay-design.md` §3). A mutual measure group is
/// one slice at its first member, keyed by every member's text; the other
/// members' slices are empty.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemSlice {
    pub source: String,
    /// Byte offset of the item in its source: every span inside the slice
    /// is relative to it when the slice is replayed at another position.
    pub start: usize,
    pub psi: std::ops::Range<usize>,
    pub events: std::ops::Range<usize>,
    pub warnings: std::ops::Range<usize>,
    /// The sealed proofs elaborating and checking the item opened, by
    /// absolute Ψ index, ascending (`heather_kernel::unseal`). The item's
    /// slice replays only while every one of them is unchanged.
    pub unsealed: Vec<usize>,
}

/// What a sliced pass did with the previous delta's items.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SliceReport {
    /// Items reproduced from the previous delta without elaboration.
    pub replayed: usize,
    /// Items elaborated from source.
    pub elaborated: usize,
    /// Items elaborated because `--only` named them
    /// (`docs/check-only-design.md`); counted in `elaborated` too.
    pub forced: usize,
}

/// The previous delta a module pass may replay slices from, and whether the
/// semantic prefix built so far is still exactly the one those slices were
/// elaborated over (`docs/declaration-slice-replay-design.md` §4).
#[derive(Clone)]
pub(crate) struct SlicePlan {
    pub(crate) previous: Rc<ModuleDelta>,
    pub(crate) exact: bool,
    pub(crate) report: SliceReport,
    /// Item names that must be elaborated from source however exact the
    /// prefix is (`docs/check-only-design.md` §2); `met` collects the ones
    /// the pass actually saw, so the caller can name the ones it did not.
    pub(crate) force: std::collections::BTreeSet<String>,
    pub(crate) met: std::collections::BTreeSet<String>,
    /// Absolute Ψ indices whose sealed proof differs from the one the
    /// previous delta's world had: a theorem whose proof was edited, in this
    /// module or a dependency. The prefix can be exact with these present —
    /// a theorem's binding leaves its proof out — and an old slice that
    /// opened one of them is elaborated instead of replayed.
    pub(crate) changed: std::collections::BTreeSet<usize>,
}

/// The journal's marks at an item's start, taken relative to the module's
/// base so the slice's ranges index the delta's vectors.
#[derive(Clone, Copy)]
pub(crate) struct SliceMark {
    psi: usize,
    events: usize,
    warnings: usize,
}

impl ModuleDelta {
    pub fn module(&self) -> &str {
        &self.module
    }

    /// The sealed proof of the extension's binding at index `k`.
    pub(crate) fn sealed_at(&self, k: usize) -> Option<&Rc<SealedProof>> {
        self.sealed.binary_search_by_key(&k, |(i, _)| *i).ok().map(|i| &self.sealed[i].1)
    }

    /// The sealed proofs of the extension range `range`, re-indexed from its
    /// start, as [`Elaborator::recheck_extension`] takes them.
    pub(crate) fn sealed_in(&self, range: std::ops::Range<usize>) -> Vec<(usize, Rc<SealedProof>)> {
        self.sealed
            .iter()
            .filter(|(i, _)| range.contains(i))
            .map(|(i, t)| (i - range.start, Rc::clone(t)))
            .collect()
    }

    /// The dependency proofs this module computed with
    /// ([`ModuleDelta::opened_dependencies`]), by absolute Ψ index.
    pub fn opened_dependency_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.opened_dependencies.iter().map(|(i, _)| *i)
    }

    pub fn binding_count(&self) -> usize {
        self.extension.len()
    }

    /// The per-item slices, in source order.
    pub fn items(&self) -> &[ItemSlice] {
        &self.items
    }

    /// The ordered dependency identity this delta was elaborated over.
    pub fn dependencies(&self) -> &ModuleDependencyIdentity {
        &self.dependencies
    }

    /// Attach the warnings an image stored beside this delta, so its slices
    /// can re-raise them (`docs/declaration-slice-replay-design.md` §4).
    /// Rejected when a slice's warning range does not fit.
    pub fn with_warnings(mut self, warnings: Vec<crate::diagnostics::Warning>) -> Result<Self, &'static str> {
        let mut at = 0;
        for slice in &self.items {
            if slice.warnings.start != at || slice.warnings.end > warnings.len() {
                return Err("slices do not partition the warnings");
            }
            at = slice.warnings.end;
        }
        if !self.items.is_empty() && at != warnings.len() {
            return Err("slices do not cover the warnings");
        }
        self.warnings = warnings;
        Ok(self)
    }

    /// The module's warnings, in order.
    pub fn warnings(&self) -> &[crate::diagnostics::Warning] {
        &self.warnings
    }

    /// The stored Ψ suffix, outermost first: what a replay rechecks or has
    /// the declaration gate vouch for.
    pub fn extension(&self) -> &[GlobalBinding] {
        &self.extension
    }

    /// The suffix, mutable — for a negative control that forges a stored
    /// binding and expects the replay to refuse it. Nothing else edits a
    /// delta after elaboration.
    #[doc(hidden)]
    pub fn extension_mut(&mut self) -> &mut Vec<GlobalBinding> {
        &mut self.extension
    }

    /// Encode this checked, process-local delta as a deterministic semantic
    /// module image. The dependency kernel prefix itself is deliberately not
    /// serialized; only its length and the loader-supplied interface
    /// identities enter the image.
    pub fn to_image_bytes(&self) -> Vec<u8> {
        crate::module_image::encode_delta(self)
    }

    /// [`Self::to_image_bytes`] together with the syntax-node count the
    /// reader charges against [`crate::ModuleImageLimits::max_nodes`] when
    /// decoding it. A publisher checks the count first: an image past the
    /// budget is decoded up to the budget and refused on every later run.
    pub fn to_image(&self) -> (Vec<u8>, u64) {
        crate::module_image::encode_delta_counted(self)
    }

    /// Deterministic downstream-observable projection used for module
    /// interface identity. Unlike the replay image, this canonicalizes source
    /// spans and opaque proof bodies while retaining transparent definitions
    /// and frontend registries consulted by dependent elaboration.
    pub fn to_interface_bytes(&self) -> Vec<u8> {
        crate::module_image::encode_delta_interface(self)
    }

    /// Decode an inert module image against an already accepted dependency
    /// kernel prefix. This allocates no unchecked collection beyond `limits`
    /// and does not mutate an elaborator; publication still goes through
    /// [`Elaborator::replay_module_delta`].
    pub fn from_image_bytes(
        bytes: &[u8],
        dependency_psi: GlobalCtx,
        limits: crate::ModuleImageLimits,
    ) -> Result<Self, crate::ModuleImageDecodeError> {
        crate::module_image::decode_delta(bytes, dependency_psi, limits)
    }
}

/// Append `bindings` to `psi` with the sealed proofs `sealed` (indexed from
/// the first of them) kept beside their theorems.
pub(crate) fn extend_sealed(psi: &mut GlobalCtx, bindings: &[GlobalBinding], sealed: &[(usize, Rc<SealedProof>)]) {
    let base = psi.bindings.len();
    psi.extend(bindings.iter().cloned());
    for (k, proof) in sealed {
        psi.seal_kept(base + k, Rc::clone(proof));
    }
}

#[derive(Debug)]
pub enum ModuleReplayError {
    DependencyIdentity,
    DependencyKernelPrefix,
    Kernel(TypeError),
    KernelWorkerPanicked,
    MetadataConflict(&'static str),
    /// A dependency theorem's sealed proof that the module opened is not the
    /// proof it opened (`ModuleDelta::opened_dependencies`): an ordinary
    /// miss — the statement is the same, the computation is not.
    OpenedProofChanged,
}

impl fmt::Display for ModuleReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DependencyIdentity => write!(f, "module dependency identity does not match"),
            Self::DependencyKernelPrefix => {
                write!(f, "module dependency kernel prefix does not match")
            }
            Self::Kernel(error) => write!(f, "stored module binding was rejected: {error:?}"),
            Self::KernelWorkerPanicked => {
                write!(f, "a kernel worker panicked rechecking a stored module binding")
            }
            Self::MetadataConflict(registry) => {
                write!(f, "stored module metadata conflicts with the accepted {registry} registry")
            }
            Self::OpenedProofChanged => {
                write!(f, "a dependency theorem the module computed with has a different proof")
            }
        }
    }
}

impl std::error::Error for ModuleReplayError {}

#[derive(Clone)]
pub(crate) enum DeltaEvent {
    Name { name: String, kind: NameKind },
    Global {
        abs: u32,
        registration: GlobalRegistration,
        is_axiom: bool,
        direct_dependencies: Vec<String>,
    },
    GenDef { key: GenDef, abs: u32 },
    /// The four guard-copy events carry `at`: the Ψ length their kernel
    /// payloads were built at, which their free globals count from. The
    /// registry ignores it (a guard copy is compared raw); relocating a
    /// module onto another world needs it
    /// (`docs/module-interface-cutoff-design.md` §3). `GenWfSlots`'s
    /// decoded copy is the exception, scoped at `D#shape`'s own position.
    GenTyCode {
        tag: u32,
        inline: Rc<Type>,
        level: Level,
        at: u32,
    },
    GenTyCodeFn {
        tag: u32,
        entry: TyCodeFn,
        at: u32,
    },
    GenWfSlots {
        tag: u32,
        slots: WfSlots,
        at: u32,
    },
    GenSpineCodes {
        tag: u32,
        codes: SpineCodes,
        at: u32,
    },
    GenFamLevels {
        tag: u32,
        level: Level,
        index_level: Level,
    },
    Inductive { module: String, info: Rc<Inductive> },
    Class { key: String, info: ClassInfo },
    Instance { key: InstKey, info: InstanceInfo },
    Designation {
        key: (OpFixity, String, String),
        info: DesignationInfo,
    },
    Derived(DerivedInst),
    Evidence(EvidenceRule),
    Repr {
        key: DatareprKey,
        name: String,
        info: DatareprInfo,
        monomorph: Option<(u32, String)>,
        obligations: Vec<Obligation>,
    },
    Impl {
        repr: String,
        op: String,
        entry: ImplEntry,
        obligations: Vec<Obligation>,
    },
    Access { designed: String, minted: String },
    InternalAccess { minted: String, owner: String },
    Meta {
        module: String,
        name: String,
        slot: Option<Slot>,
        definition: MetaDef,
    },
}

#[derive(Clone)]
pub(crate) struct ModuleJournal {
    pub(crate) events: Vec<DeltaEvent>,
    /// Ψ length and warning count when the journal was installed: the
    /// delta's vectors start here.
    pub(crate) base_psi: usize,
    pub(crate) base_warnings: usize,
    pub(crate) items: Vec<ItemSlice>,
    pub(crate) scope_at_entry: Option<Scope>,
    /// Sealed proofs opened by kernel checks that ran on the pool, keyed by
    /// the Ψ length each was queued at, charged to their items' slices when
    /// the delta is built (a join may come after the item's slice closed).
    pub(crate) deferred_unseals: Vec<(usize, Vec<usize>)>,
}

impl ModuleJournal {
    fn new(base_psi: usize, base_warnings: usize) -> Self {
        Self {
            events: Vec::new(),
            base_psi,
            base_warnings,
            items: Vec::new(),
            scope_at_entry: None,
            deferred_unseals: Vec::new(),
        }
    }

    fn lengths(&self) -> (usize, usize) {
        (self.events.len(), self.items.len())
    }
}

/// The elaborator's journal slot. A clone of the elaborator is a probe or a
/// snapshot, never a second recorder of the same module: it gets no journal,
/// only the lengths the live one had. So a clone is O(1) however much the
/// module has recorded — a deep copy made every speculative probe
/// (`type_endpoint_can_anchor`, operator carriers, measure queries) linear
/// in the events so far, which made a large module quadratic on the
/// delta path (issues/check-module-delta-certificate-cost.md) — and a
/// probe's registrations are discarded with it, as its Ψ is.
/// [`Elaborator::restore_from_clone`] truncates the live journal back to the
/// snapshot's lengths, the way a failed [`Elaborator::session_transaction`]
/// does.
pub(crate) struct JournalSlot {
    live: RefCell<Option<ModuleJournal>>,
    mark: Option<(usize, usize)>,
}

impl JournalSlot {
    pub(crate) fn new() -> Self {
        Self { live: RefCell::new(None), mark: None }
    }

    /// The live journal a restored snapshot keeps: `live` cut back to the
    /// lengths this (snapshot) slot recorded when it was cloned.
    pub(crate) fn restore(&mut self, live: Option<ModuleJournal>) {
        *self.live.get_mut() = self.mark.zip(live).map(|((events, items), mut journal)| {
            journal.events.truncate(events);
            journal.items.truncate(items);
            journal
        });
        self.mark = None;
    }

    pub(crate) fn take(&mut self) -> Option<ModuleJournal> {
        self.live.get_mut().take()
    }
}

impl Clone for JournalSlot {
    fn clone(&self) -> Self {
        Self { live: RefCell::new(None), mark: self.live.borrow().as_ref().map(ModuleJournal::lengths) }
    }
}

impl std::ops::Deref for JournalSlot {
    type Target = RefCell<Option<ModuleJournal>>;

    fn deref(&self) -> &Self::Target {
        &self.live
    }
}

impl Elaborator {
    /// Append one journal event only while extracting a module. Taking a
    /// closure keeps payload cloning off every ordinary source-elaboration
    /// path and off replay itself.
    pub(crate) fn record_module_event(&self, event: impl FnOnce() -> DeltaEvent) {
        if let Some(journal) = self.module_journal.borrow_mut().as_mut() {
            journal.events.push(event());
        }
    }

    pub(crate) fn semantic_commit_name(&mut self, name: &str, kind: NameKind) {
        self.record_module_event(|| DeltaEvent::Name {
            name: name.to_string(),
            kind,
        });
        self.names.insert_current(name, kind);
    }

    pub(crate) fn semantic_commit_global(
        &mut self,
        abs: u32,
        registration: GlobalRegistration,
        is_axiom: bool,
        direct_dependencies: Vec<String>,
    ) {
        self.record_module_event(|| DeltaEvent::Global {
            abs,
            registration: registration.clone(),
            is_axiom,
            direct_dependencies: direct_dependencies.clone(),
        });
        let key = registration.key.clone();
        self.names.commit_global(abs, registration);
        self.provenance.commit(key, is_axiom, direct_dependencies);
    }

    pub(crate) fn semantic_commit_gen_def(&mut self, key: GenDef, abs: u32) {
        self.record_module_event(|| DeltaEvent::GenDef { key, abs });
        self.types.gdefs_mut().insert_binding(key, abs);
    }

    pub(crate) fn semantic_commit_gen_ty_code(
        &mut self,
        tag: u32,
        inline: Rc<Type>,
        level: Level,
        at: u32,
    ) {
        self.record_module_event(|| DeltaEvent::GenTyCode {
            tag,
            inline: Rc::clone(&inline),
            level: level.clone(),
            at,
        });
        if crate::gendefs::mentions_global(&inline) {
            self.types.gdefs_mut().insert_guard_at(crate::gendefs::GuardKey::TyCode(tag), at);
        }
        self.types.gdefs_mut().insert_ty_code(tag, (inline, level));
    }

    pub(crate) fn semantic_commit_gen_ty_code_fn(&mut self, tag: u32, entry: TyCodeFn, at: u32) {
        self.record_module_event(|| DeltaEvent::GenTyCodeFn {
            tag,
            entry: entry.clone(),
            at,
        });
        self.types.gdefs_mut().insert_ty_code_fn(tag, entry);
    }

    pub(crate) fn semantic_commit_gen_wf_slots(&mut self, tag: u32, slots: WfSlots, at: u32) {
        self.record_module_event(|| DeltaEvent::GenWfSlots {
            tag,
            slots: slots.clone(),
            at,
        });
        if crate::gendefs::mentions_global(&slots.shape) || slots.arity.shift_global(1) != *slots.arity {
            self.types.gdefs_mut().insert_guard_at(crate::gendefs::GuardKey::WfSlots(tag), at);
        }
        self.types.gdefs_mut().insert_wf_slots(tag, slots);
    }

    pub(crate) fn semantic_commit_gen_spine_codes(&mut self, tag: u32, codes: SpineCodes, at: u32) {
        self.record_module_event(|| DeltaEvent::GenSpineCodes {
            tag,
            codes: codes.clone(),
            at,
        });
        if codes.ctors.iter().chain(&codes.nodes).any(|(ty, _)| crate::gendefs::mentions_global(ty)) {
            self.types.gdefs_mut().insert_guard_at(crate::gendefs::GuardKey::Spine(tag), at);
        }
        self.types.gdefs_mut().insert_spine_codes(tag, codes);
    }

    pub(crate) fn semantic_commit_gen_fam_levels(
        &mut self,
        tag: u32,
        level: Level,
        index_level: Level,
    ) {
        self.record_module_event(|| DeltaEvent::GenFamLevels {
            tag,
            level: level.clone(),
            index_level: index_level.clone(),
        });
        self.types
            .gdefs_mut()
            .insert_fam_levels(tag, (level, index_level));
    }

    pub(crate) fn semantic_commit_inductive(&mut self, module: String, info: Rc<Inductive>) {
        self.record_module_event(|| DeltaEvent::Inductive {
            module: module.clone(),
            info: Rc::clone(&info),
        });
        self.types.commit(&module, info);
    }

    pub(crate) fn semantic_commit_class(&mut self, key: String, info: ClassInfo) {
        self.record_module_event(|| DeltaEvent::Class {
            key: key.clone(),
            info: info.clone(),
        });
        self.traits.commit_class(key, info);
    }

    pub(crate) fn semantic_commit_instance(&mut self, key: InstKey, info: InstanceInfo) {
        self.record_module_event(|| DeltaEvent::Instance {
            key: key.clone(),
            info: info.clone(),
        });
        self.traits.commit_instance(key, info);
    }

    pub(crate) fn semantic_commit_designation(
        &mut self,
        key: (OpFixity, String, String),
        info: DesignationInfo,
    ) {
        self.record_module_event(|| DeltaEvent::Designation {
            key: key.clone(),
            info: info.clone(),
        });
        self.traits.commit_designation(key, info);
    }

    pub(crate) fn semantic_commit_evidence(&mut self, rule: EvidenceRule) {
        self.record_module_event(|| DeltaEvent::Evidence(rule.clone()));
        self.traits.commit_evidence(rule);
    }

    pub(crate) fn semantic_commit_derived(&mut self, info: DerivedInst) {
        self.record_module_event(|| DeltaEvent::Derived(info.clone()));
        self.traits.commit_derived(info);
    }

    pub(crate) fn semantic_commit_repr(
        &mut self,
        key: DatareprKey,
        name: String,
        info: DatareprInfo,
        monomorph: Option<(u32, String)>,
        obligations: Vec<Obligation>,
    ) {
        self.record_module_event(|| DeltaEvent::Repr {
            key: key.clone(),
            name: name.clone(),
            info: info.clone(),
            monomorph: monomorph.clone(),
            obligations: obligations.clone(),
        });
        self.representations
            .commit_repr(key, name, info, monomorph, obligations);
    }

    pub(crate) fn semantic_commit_impl(
        &mut self,
        repr: String,
        op: String,
        entry: ImplEntry,
        obligations: Vec<Obligation>,
    ) {
        self.record_module_event(|| DeltaEvent::Impl {
            repr: repr.clone(),
            op: op.clone(),
            entry: entry.clone(),
            obligations: obligations.clone(),
        });
        self.representations.commit_impl(repr, op, entry, obligations);
    }

    pub(crate) fn semantic_commit_meta(
        &mut self,
        module: String,
        name: String,
        slot: Option<Slot>,
        definition: MetaDef,
    ) {
        self.record_module_event(|| DeltaEvent::Meta {
            module: module.clone(),
            name: name.clone(),
            slot,
            definition: definition.clone(),
        });
        self.meta_programs.commit(module, name, slot, definition);
    }

    /// Elaborate a whole module atomically and return its logical semantic
    /// delta. A later item failure rolls back successful items before it.
    pub fn elab_module_delta(
        &mut self,
        module: &str,
        src: &str,
        dependencies: ModuleDependencyIdentity,
    ) -> R<ModuleDelta> {
        assert!(
            self.module_journal.borrow().is_none(),
            "module delta extraction is not nested"
        );
        let dependency_psi = (*self.psi).clone();
        let base_len = dependency_psi.bindings.len();
        *self.module_journal.borrow_mut() =
            Some(ModuleJournal::new(base_len, self.warnings.borrow().len()));
        let result = self.session_transaction(|me| me.elab_module_source(module, src));
        let journal = self
            .module_journal
            .borrow_mut()
            .take()
            .expect("module journal was installed");
        result?;
        Ok(self.delta_from_journal(module, dependencies, dependency_psi, journal))
    }

    /// The delta the journal describes, once the module has checked.
    fn delta_from_journal(
        &self,
        module: &str,
        dependencies: ModuleDependencyIdentity,
        dependency_psi: GlobalCtx,
        journal: ModuleJournal,
    ) -> ModuleDelta {
        let base = journal.base_psi;
        let extension = self.psi.bindings.iter().skip(base).cloned().collect();
        let warnings = self.warnings.borrow()[journal.base_warnings..].to_vec();
        let sealed = self.psi.sealed.iter().filter(|(i, _)| *i >= base).map(|(i, t)| (i - base, Rc::clone(t))).collect();
        let mut items = journal.items;
        // A proof checked on the pool belongs to the item that queued it:
        // the last slice that had begun at the Ψ length it was queued at.
        for (at, opened) in journal.deferred_unseals {
            let k = items.iter().rposition(|slice| base + slice.psi.start <= at);
            if let Some(slice) = k.and_then(|k| items.get_mut(k)) {
                slice.unsealed.extend(opened);
                slice.unsealed.sort_unstable();
                slice.unsealed.dedup();
            }
        }
        let opened: std::collections::BTreeSet<usize> =
            items.iter().flat_map(|slice| slice.unsealed.iter().copied()).filter(|i| *i < base).collect();
        let opened_dependencies = opened
            .into_iter()
            .filter_map(|i| Some((i, Rc::clone(dependency_psi.sealed_kept(i)?))))
            .collect();
        ModuleDelta {
            module: module.to_string(),
            dependencies,
            dependency_psi,
            extension,
            sealed,
            opened_dependencies,
            scope: self.names.scope().clone(),
            events: journal.events,
            items,
            warnings,
            scope_at_entry: journal.scope_at_entry,
        }
    }

    /// [`Self::check_module_delta`] with the module's *previous* delta to
    /// replay unchanged items from (`docs/declaration-slice-replay-design.md`
    /// §4): an item whose source text matches the previous slice at its
    /// position, while every earlier item reproduced the previous prefix
    /// exactly, is reproduced from the slice — its bindings through the gate,
    /// its events through the preflight checks — instead of elaborated. The
    /// delta returned is what fresh elaboration would have produced.
    pub fn check_module_delta_from(
        &mut self,
        module: &str,
        src: &str,
        dependencies: ModuleDependencyIdentity,
        previous: &ModuleDelta,
    ) -> Result<(ModuleDelta, SliceReport), Vec<ElabError>> {
        self.check_module_delta_only(module, src, dependencies, previous, Default::default())
            .map(|(delta, report, _)| (delta, report))
    }

    /// [`Self::check_module_delta_from`] with `force`: the named items are
    /// elaborated from source whether or not their slice would replay, so a
    /// probe can time one declaration over a replayed prefix
    /// (`docs/check-only-design.md`). A name matches an item's declared name
    /// (`item_timing_name`), and naming any member of a mutual measure
    /// group elaborates the group. The third result is the set of forced
    /// names the pass met; a caller that named something not in this module
    /// reads the difference.
    pub fn check_module_delta_only(
        &mut self,
        module: &str,
        src: &str,
        dependencies: ModuleDependencyIdentity,
        previous: &ModuleDelta,
        force: std::collections::BTreeSet<String>,
    ) -> Result<(ModuleDelta, SliceReport, std::collections::BTreeSet<String>), Vec<ElabError>> {
        assert!(self.slice_plan.is_none(), "sliced module checks are not nested");
        self.slice_plan = Some(SlicePlan {
            previous: Rc::new(previous.clone()),
            exact: false,
            report: SliceReport::default(),
            force,
            met: Default::default(),
            changed: Default::default(),
        });
        let result = self.check_module_delta(module, src, dependencies);
        let plan = self.slice_plan.take().expect("the slice plan was installed");
        result.map(|delta| (delta, plan.report, plan.met))
    }

    /// Is any of `names` (an item's name, or a group's members' names) one
    /// the plan forces from source? Records the ones it met.
    pub(crate) fn slice_forced(&mut self, names: &[String]) -> bool {
        let Some(plan) = self.slice_plan.as_mut() else { return false };
        let mut forced = false;
        for name in names {
            if plan.force.contains(name) {
                plan.met.insert(name.clone());
                forced = true;
            }
        }
        if forced {
            plan.report.forced += 1;
        }
        forced
    }

    /// The pass just entered `module`: decide whether the previous delta's
    /// slices apply at all. They do only over the same dependency identity,
    /// the same dependency Ψ and the same entry scope — the three inputs an
    /// item's elaboration reads besides the earlier items of its module.
    pub(crate) fn slice_enter(&mut self, module: &str) {
        let scope = self.names.scope().clone();
        if let Some(journal) = self.module_journal.borrow_mut().as_mut() {
            journal.scope_at_entry = Some(scope.clone());
        }
        let Some(plan) = self.slice_plan.as_ref() else { return };
        let previous = &plan.previous;
        let exact = previous.module == module
            && previous.scope_at_entry.as_ref() == Some(&scope)
            && previous.dependency_psi.bindings.len() == self.psi.bindings.len()
            && previous.dependency_psi.bindings.iter().eq(self.psi.bindings.iter());
        // A dependency theorem whose proof changed under an unchanged
        // statement leaves the prefix exact; only the items that opened it
        // have to be elaborated again.
        let changed = previous
            .opened_dependencies
            .iter()
            .filter(|(i, old)| self.psi.sealed_kept(*i).is_none_or(|now| !same_proof(now, old)))
            .map(|(i, _)| *i)
            .collect();
        let plan = self.slice_plan.as_mut().expect("checked above");
        plan.exact = exact;
        plan.report = SliceReport::default();
        plan.changed = changed;
    }

    pub(crate) fn slice_begin(&self) -> Option<SliceMark> {
        let journal = self.module_journal.borrow();
        let journal = journal.as_ref()?;
        Some(SliceMark {
            psi: self.psi.bindings.len() - journal.base_psi,
            events: journal.events.len(),
            warnings: self.warnings.borrow().len() - journal.base_warnings,
        })
    }

    /// Close the slice an item opened with [`Self::slice_begin`], after
    /// everything the item contributes (its derived instances included) has
    /// landed, and keep the plan's `exact` flag honest: it means the prefix
    /// through the items completed so far equals the previous delta's, so
    /// the next item may replay its slice (§4).
    pub(crate) fn slice_end(
        &mut self,
        mark: SliceMark,
        source: String,
        start: usize,
        replayed: bool,
        unsealed: Vec<usize>,
    ) {
        let Some(begun) = self.slice_begin() else { return };
        let mut unsealed = unsealed;
        if replayed {
            // A replayed slice computed with what its first elaboration
            // opened, whatever its recheck opened now.
            let index = self.module_journal.borrow().as_ref().map_or(0, |j| j.items.len());
            if let Some(old) = self.slice_plan.as_ref().and_then(|p| p.previous.items.get(index)) {
                unsealed.extend(old.unsealed.iter().copied());
                unsealed.sort_unstable();
                unsealed.dedup();
            }
        }
        let slice = ItemSlice {
            source,
            start,
            psi: mark.psi..begun.psi,
            events: mark.events..begun.events,
            warnings: mark.warnings..begun.warnings,
            unsealed,
        };
        let index = {
            let mut journal = self.module_journal.borrow_mut();
            let journal = journal.as_mut().expect("slice_begin found a journal");
            journal.items.push(slice.clone());
            journal.items.len() - 1
        };
        let Some(plan) = self.slice_plan.as_ref() else { return };
        if !plan.exact || replayed {
            // A broken prefix stays broken: everything after the first item
            // whose contribution differed sits over a different world. A
            // replayed slice reproduced the previous one by construction.
            return;
        }
        // The item was elaborated from source over an exact prefix. The
        // prefix stays exact only if its contribution equals the previous
        // slice's at this position — which is what a proof-body edit, a
        // comment, or reformatting leaves behind, and what a changed `fn`
        // body does not.
        let previous = Rc::clone(&plan.previous);
        let same = previous.items.get(index).is_some_and(|old| {
            let journal = self.module_journal.borrow();
            let journal = journal.as_ref().expect("slice_begin found a journal");
            old.psi == slice.psi
                && old.events == slice.events
                && previous.extension[old.psi.clone()].iter().eq(
                    self.psi.bindings.iter().skip(journal.base_psi + slice.psi.start).take(slice.psi.len()),
                )
                && crate::module_image::encode_events(&previous.events[old.events.clone()], true)
                    == crate::module_image::encode_events(&journal.events[slice.events.clone()], true)
        });
        if !same {
            self.slice_plan.as_mut().expect("checked above").exact = false;
            return;
        }
        // The same bindings and events: the prefix stays exact. A theorem
        // whose proof was edited is the case this exists for, and the
        // later items that opened that proof are the ones that must not
        // replay.
        let base = self.module_journal.borrow().as_ref().map_or(0, |j| j.base_psi);
        let old = &previous.items[index];
        let mut changed = Vec::new();
        for k in 0..slice.psi.len() {
            let before = previous.sealed_at(old.psi.start + k);
            let now = self.psi.sealed_kept(base + slice.psi.start + k);
            let same = match (before, now) {
                (None, None) => true,
                (Some(a), Some(b)) => same_proof(a, b),
                _ => false,
            };
            if !same {
                changed.push(base + slice.psi.start + k);
            }
        }
        self.slice_plan.as_mut().expect("checked above").changed.extend(changed);
    }

    /// Try to reproduce item `index` from the previous delta's slice. `true`
    /// means the slice landed (Ψ, events, warnings) and the item is done;
    /// `false` means elaborate it. A slice the gate or the preflight checks
    /// refuse is rolled back and the item is elaborated instead.
    pub(crate) fn try_replay_slice(&mut self, index: usize, source: &str, start: usize) -> bool {
        let Some(plan) = self.slice_plan.as_ref() else { return false };
        if !plan.exact {
            return false;
        }
        let previous = Rc::clone(&plan.previous);
        // A text mismatch is not a broken prefix: the item is elaborated,
        // and `slice_end` decides from what it contributed.
        let Some(old) = previous.items.get(index).filter(|old| old.source == source) else {
            return false;
        };
        // An item that opened a proof which has changed since is elaborated
        // again: what it computed with is not what it would compute with
        // now. Its text is unchanged, so this does not break the prefix;
        // `slice_end` decides that from what it contributes.
        if old.unsealed.iter().any(|i| plan.changed.contains(i)) {
            return false;
        }
        // Not in a `session_transaction`: `replay_slice` fails only before its
        // first write, so a refused slice leaves nothing to roll back. A
        // checkpoint would be worse than redundant — holding the committed
        // world makes the slice's first write copy every registry's current
        // module layer, so each replayed item cost O(module) and a large
        // module replayed slower than it elaborated
        // (issues/check-module-delta-certificate-cost.md).
        let replayed = self.replay_slice(&previous, old, start);
        let plan = self.slice_plan.as_mut().expect("checked above");
        match replayed {
            Ok(()) => {
                plan.report.replayed += 1;
                true
            }
            Err(_) => {
                plan.exact = false;
                false
            }
        }
    }

    /// An item was elaborated from source under a slice plan.
    pub(crate) fn slice_elaborated(&mut self) {
        if let Some(plan) = self.slice_plan.as_mut() {
            plan.report.elaborated += 1;
        }
    }

    /// Every fallible step — the recheck, the relocation, the preflight
    /// checks — comes before the first write, so a refused slice leaves the
    /// elaborator as it found it; [`Self::try_replay_slice`] relies on that
    /// instead of a checkpoint. Keep it so.
    fn replay_slice(
        &mut self,
        previous: &ModuleDelta,
        slice: &ItemSlice,
        start: usize,
    ) -> Result<(), ModuleReplayError> {
        let bindings = &previous.extension[slice.psi.clone()];
        let sealed = previous.sealed_in(slice.psi.clone());
        // Inline, whatever the pool's width: the pool holds the bodies of the
        // items elaborated around this one, and their join is the module's.
        self.recheck_extension(&previous.module, bindings, &sealed, false, &mut true)?;
        // The item's text is unchanged but may sit elsewhere in the file:
        // every span the slice carries moves with it.
        let offset = start as i64 - slice.start as i64;
        let events = crate::module_image::relocate_events(&previous.events[slice.events.clone()], offset)
            .map_err(|_| ModuleReplayError::MetadataConflict("relocated slice"))?;
        for event in &events {
            self.preflight_module_event(event)?;
        }
        extend_sealed(&mut self.psi, bindings, &sealed);
        for event in events {
            // Applying an event records it again, so the new delta's journal
            // carries this slice as it would a fresh elaboration's.
            self.apply_module_event(event);
        }
        self.refresh_delta_psi();
        self.result_only_memo.borrow_mut().clear();
        self.named_type_memo.borrow_mut().clear();
        let shift = |at: usize| (at as i64 + offset) as usize;
        self.warnings.borrow_mut().extend(previous.warnings[slice.warnings.clone()].iter().map(|w| {
            let mut w = w.clone();
            w.span = heather_syntax::Span { start: shift(w.span.start), end: shift(w.span.end) };
            if let Some(fix) = w.fix.as_mut() {
                fix.span = heather_syntax::Span { start: shift(fix.span.start), end: shift(fix.span.end) };
            }
            w
        }));
        Ok(())
    }

    /// Check a whole module with the ordinary diagnostic-recovery policy and,
    /// when every item succeeds, return the same logical delta as
    /// [`Self::elab_module_delta`].
    ///
    /// Unlike the atomic extraction entry point, a failing module keeps the
    /// successful items around so later items can still be diagnosed. This is
    /// the CLI `check` contract; the discarded journal merely means there is
    /// no reusable image for a module which did not check completely.
    pub fn check_module_delta(
        &mut self,
        module: &str,
        src: &str,
        dependencies: ModuleDependencyIdentity,
    ) -> Result<ModuleDelta, Vec<ElabError>> {
        assert!(
            self.module_journal.borrow().is_none(),
            "module delta extraction is not nested"
        );
        let dependency_psi = (*self.psi).clone();
        let base_len = dependency_psi.bindings.len();
        *self.module_journal.borrow_mut() =
            Some(ModuleJournal::new(base_len, self.warnings.borrow().len()));
        let errs = self.check_module_source_inner(module, src);
        let journal = self
            .module_journal
            .borrow_mut()
            .take()
            .expect("module journal was installed");
        if !errs.is_empty() {
            return Err(errs);
        }
        Ok(self.delta_from_journal(module, dependencies, dependency_psi, journal))
    }

    /// [`Self::check_module_delta`], keeping the delta of what checked when
    /// some declarations were refused: a refused declaration registers
    /// nothing, so the journal holds exactly the module's other items. For a
    /// module whose refusals are its point (`heather check --expectations`),
    /// whose caller judges `errors` and decides whether the delta stands
    /// for the module (`docs/module-dag-design.md` §11).
    pub fn check_module_delta_refusing(
        &mut self,
        module: &str,
        src: &str,
        dependencies: ModuleDependencyIdentity,
    ) -> (ModuleDelta, Vec<ElabError>) {
        assert!(
            self.module_journal.borrow().is_none(),
            "module delta extraction is not nested"
        );
        let dependency_psi = (*self.psi).clone();
        let base_len = dependency_psi.bindings.len();
        *self.module_journal.borrow_mut() =
            Some(ModuleJournal::new(base_len, self.warnings.borrow().len()));
        let errs = self.check_module_source_inner(module, src);
        let journal = self
            .module_journal
            .borrow_mut()
            .take()
            .expect("module journal was installed");
        (self.delta_from_journal(module, dependencies, dependency_psi, journal), errs)
    }

    /// Recheck the stored suffix, install metadata into a private candidate,
    /// and publish the candidate only after every operation succeeds.
    pub fn replay_module_delta(
        &mut self,
        delta: &ModuleDelta,
        dependencies: &ModuleDependencyIdentity,
    ) -> Result<(), ModuleReplayError> {
        self.replay_module_delta_keyed(delta, dependencies, None)
    }

    /// [`Self::replay_module_delta`] with `replay`, an identity of this exact
    /// replay that its caller vouches for: the stored bytes the delta was
    /// decoded from and the world it is replayed over, module by module
    /// (`docs/module-dag-design.md` §13). A gate that has seen the identity
    /// pass skips the recheck of the whole extension; one whose recheck
    /// passes without opening a sealed proof records it. Everything else a
    /// replay checks (the dependency identity, opened proofs, exports, the
    /// metadata preflight) is checked either way.
    pub fn replay_module_delta_keyed(
        &mut self,
        delta: &ModuleDelta,
        dependencies: &ModuleDependencyIdentity,
        replay: Option<&[u8; 32]>,
    ) -> Result<(), ModuleReplayError> {
        if dependencies != &delta.dependencies {
            return Err(ModuleReplayError::DependencyIdentity);
        }
        if self.psi.bindings.iter().ne(delta.dependency_psi.bindings.iter()) {
            return Err(ModuleReplayError::DependencyKernelPrefix);
        }
        // The module computed with these dependency proofs; a dependency
        // whose proof changed under the same statement has the same
        // interface, so this is the one place that notices.
        if delta
            .opened_dependencies
            .iter()
            .any(|(i, old)| self.psi.sealed_kept(*i).is_none_or(|now| !same_proof(now, old)))
        {
            return Err(ModuleReplayError::OpenedProofChanged);
        }
        if !self.names.valid_exports(&delta.scope) {
            return Err(ModuleReplayError::MetadataConflict("reexports"));
        }
        let gate = self.gate.clone();
        match (&gate, replay) {
            (Some(g), Some(key)) if g.admits_replay(key) => {}
            _ => {
                let mut clean = true;
                self.recheck_extension(&delta.module, &delta.extension, &delta.sealed, true, &mut clean)?;
                if let (Some(g), Some(key), true) = (&gate, replay, clean) {
                    g.replay_accepted(key);
                }
            }
        }

        let mut candidate = self.semantic_image().elaborator();
        candidate.names.enter_scope(delta.scope.clone());
        extend_sealed(&mut candidate.psi, &delta.extension, &delta.sealed);
        // Check every operation against the dependency world before applying
        // any of them. Some one-module commits intentionally share a logical
        // name across correlated registries; intra-delta duplicates were
        // already rejected by the image decoder.
        for event in &delta.events {
            candidate.preflight_module_event(event)?;
        }
        for event in delta.events.iter().cloned() {
            candidate.apply_module_event(event);
        }
        candidate.refresh_delta_psi();
        self.committed = candidate.committed;
        self.result_only_memo.borrow_mut().clear();
        self.named_type_memo.borrow_mut().clear();
        Ok(())
    }

    /// `⊢_L Ψ, Ψ'` for the stored suffix — the kernel recheck of a replayed
    /// module, on the kernel worker pool when the elaborator has one, and
    /// through the installed gate oracle when there is one.
    ///
    /// The serial form is one `typing::check_global_ctx_extension` call. The
    /// wide form is the same judgement split the way the deferred gate splits
    /// a fresh declaration (`docs/parallel-kernel-gate-design.md` §2): each
    /// binding's *statement* is checked here, in order, and each definition's
    /// *body* is queued as a `check_term` against the frozen prefix it sits
    /// over. The prefix is an O(1) snapshot per binding (`GlobalBindings` is
    /// persistent), and the bodies are independent of one another by
    /// construction — a body is scoped over its own prefix and nothing after
    /// it. Every queued body is joined before this returns, so a replay is
    /// accepted only when the kernel accepted all of it, and the pool is
    /// quiescent for whatever the caller does next. Nothing is committed
    /// from a rejected replay at either width; the caller rebuilds the
    /// module from source instead.
    ///
    /// **The gate vouches here exactly as it does at the source gate.** A
    /// stored definition is the binding the cold run's `GateItem::binding`
    /// produced, over the same Ψ prefix, so it asks the oracle the same
    /// question (`docs/cache-v1-design.md` §3: the name is metadata, not
    /// identity) and an `admits` hit skips its statement and body the way it
    /// does for a fresh declaration; a miss is checked and `accepted` at the
    /// same points the source path uses. A theorem is stored without its
    /// proof, so it asks about its statement alone
    /// ([`crate::gate::KernelGate::admits_statement`]). Before
    /// 2026-09-17 a replay rechecked every stored body regardless, so a warm
    /// run of an unchanged file cost more than an edited one
    /// (`issues/semantic-replay-phase-attribution.md`).
    fn recheck_extension(
        &mut self,
        module: &str,
        extension: &[GlobalBinding],
        sealed: &[(usize, Rc<SealedProof>)],
        on_pool: bool,
        clean: &mut bool,
    ) -> Result<(), ModuleReplayError> {
        let gate = self.gate.clone();
        // `on_pool == false` keeps every body on this thread even at width:
        // a slice replay runs inside a module pass whose own deferred bodies
        // are on the pool, and a join here would consume their outcomes.
        let inline = self.kernel_pool.is_inline() || !on_pool;
        // The one-call form checks bindings alone, and a definition that
        // computes with an earlier theorem's witness needs its sealed proof
        // in the prefix: with any, take the per-binding loop below.
        if gate.is_none() && inline && sealed.is_empty() {
            return typing::check_global_ctx_extension(&self.psi, extension, 0, self.fuel)
                .map_err(ModuleReplayError::Kernel);
        }
        let mut prefix = Rc::clone(&self.psi.0);
        let mut statement = Ok(());
        for (index, binding) in extension.iter().enumerate() {
            // The oracle's human-readable column only; identity is the
            // content hash, and a stored binding has no source name here.
            let name = format!("{module}#{index}");
            let body = match binding {
                GlobalBinding::Tm { ctx, layer, ty, level, body: Some(body) } => {
                    Some(crate::gate::GateItem {
                        name: &name,
                        ctx,
                        ty,
                        level,
                        body,
                        opaque: false,
                        layer: *layer,
                        lands_in_psi: true,
                    })
                }
                _ => None,
            };
            // A declaration without a body (a theorem's statement, an opaque
            // one) has no check key, but its statement has a verdict of its
            // own: without one every load re-checked every such statement,
            // which was the whole of a warm world's `image_recheck`
            // (`issues/native-process-fixed-cost.md`).
            let bodiless = matches!(binding, GlobalBinding::Tm { body: None, .. });
            let admitted = match (&gate, &body) {
                (Some(g), Some(item)) => g.admits(&prefix, item),
                (Some(g), None) if bodiless => g.admits_statement(&prefix, binding),
                _ => false,
            };
            if !admitted {
                let (checked, unsealed) = heather_kernel::unseal::record(|| {
                    typing::check_global_binding_statement(&prefix, binding, 0, self.fuel)
                });
                if let Err(e) = checked {
                    statement = Err(ModuleReplayError::Kernel(e));
                    break;
                }
                // `clean`: no check this replay ran opened a sealed proof,
                // so a verdict about the whole replay may be kept on the
                // same rule as one about a declaration.
                *clean &= unsealed.is_empty();
                if let (Some(g), true) = (&gate, bodiless) {
                    g.statement_accepted(&prefix, binding, &unsealed);
                }
                if let Some(item) = &body {
                    if inline {
                        let (verdict, unsealed) = heather_kernel::unseal::record(|| {
                            typing::check_term(
                                &prefix, 0, item.layer, item.ctx, item.body, item.ty, item.level, self.fuel,
                            )
                        });
                        if let Err(e) = verdict {
                            statement = Err(ModuleReplayError::Kernel(e));
                            break;
                        }
                        *clean &= unsealed.is_empty();
                        if let Some(g) = &gate {
                            g.accepted(&prefix, item, &unsealed);
                        }
                    } else {
                        // Its seals are known only at the join.
                        *clean = false;
                        self.kernel_pool.submit(pool::Deferred {
                            name: name.clone(),
                            span: heather_syntax::Span { start: 0, end: 0 },
                            psi: Rc::clone(&prefix),
                            ctx: item.ctx.clone(),
                            ty: item.ty.clone(),
                            level: item.level.clone(),
                            body: item.body.clone(),
                            opaque: false,
                            layer: item.layer,
                            lands_in_psi: true,
                            fuel: self.fuel,
                            unsealed: Vec::new(),
                            row: None,
                        });
                    }
                }
            }
            drop(body);
            let at = prefix.bindings.len();
            let psi = crate::stats::make_mut(&mut prefix);
            psi.push(binding.clone());
            if let Ok(k) = sealed.binary_search_by_key(&index, |(k, _)| *k) {
                psi.seal_kept(at, Rc::clone(&sealed[k].1));
            }
        }
        // Join even after a statement failure: the pool must be drained before
        // the caller moves on, and a body verdict is still a verdict. But only
        // what this call queued — nothing, when inline. A slice replay runs
        // inside a module pass whose own deferred bodies are on the pool, and
        // a join here took *their* outcomes: a rejected proof before the slice
        // became this replay's failure, the item was elaborated instead, and
        // the pass's own join found nothing to refuse the module with.
        let outcomes = if inline { Vec::new() } else { self.kernel_pool.join() };
        let mut body = Ok(());
        for outcome in &outcomes {
            // The workers' counters fold into the module row as the gate's do;
            // their clocks are not charged anywhere, because the enclosing
            // `image_recheck` bracket is wall and already holds this join.
            stats::fold_deferred_kernel(None, outcome.ns, &outcome.kernel);
            if body.is_ok() {
                if let Err(err) = &outcome.verdict {
                    body = Err(match err {
                        Some(err) => ModuleReplayError::Kernel(*err),
                        None => ModuleReplayError::KernelWorkerPanicked,
                    });
                }
            }
        }
        // A statement failure at index i precedes any body failure at j ≥ i
        // in the serial order, and every body before i passed the statement
        // check; the first failure by binding order is what the serial form
        // reports, and it is the statement's when both exist.
        let verdict = statement.and(body);
        if let Some(g) = &gate {
            match &verdict {
                Ok(()) => {
                    // Every queued body passed: record each at the Ψ it was
                    // queued against, as the source join does.
                    for outcome in &outcomes {
                        let item = outcome.item.as_ref();
                        g.accepted(
                            &item.psi,
                            &crate::gate::GateItem {
                                name: &item.name,
                                ctx: &item.ctx,
                                ty: &item.ty,
                                level: &item.level,
                                body: &item.body,
                                opaque: item.opaque,
                                layer: item.layer,
                                lands_in_psi: item.lands_in_psi,
                            },
                            &outcome.unsealed,
                        );
                    }
                }
                // Nothing lands from a rejected replay, so every question this
                // replay opened is dead; the rebuild from source asks its own.
                Err(_) => g.abandon(&self.psi),
            }
        }
        verdict
    }

    fn apply_module_event(&mut self, event: DeltaEvent) {
        match event {
            DeltaEvent::Name { name, kind } => self.semantic_commit_name(&name, kind),
            DeltaEvent::Global { abs, registration, is_axiom, direct_dependencies } => {
                self.semantic_commit_global(abs, registration, is_axiom, direct_dependencies);
            }
            DeltaEvent::GenDef { key, abs } => self.semantic_commit_gen_def(key, abs),
            DeltaEvent::GenTyCode { tag, inline, level, at } => {
                self.semantic_commit_gen_ty_code(tag, inline, level, at);
            }
            DeltaEvent::GenTyCodeFn { tag, entry, at } => {
                self.semantic_commit_gen_ty_code_fn(tag, entry, at);
            }
            DeltaEvent::GenWfSlots { tag, slots, at } => {
                self.semantic_commit_gen_wf_slots(tag, slots, at);
            }
            DeltaEvent::GenSpineCodes { tag, codes, at } => {
                self.semantic_commit_gen_spine_codes(tag, codes, at);
            }
            DeltaEvent::GenFamLevels { tag, level, index_level } => {
                self.semantic_commit_gen_fam_levels(tag, level, index_level);
            }
            DeltaEvent::Inductive { module, info } => {
                self.semantic_commit_inductive(module, info);
            }
            DeltaEvent::Class { key, info } => self.semantic_commit_class(key, info),
            DeltaEvent::Instance { key, info } => self.semantic_commit_instance(key, info),
            DeltaEvent::Designation { key, info } => self.semantic_commit_designation(key, info),
            DeltaEvent::Derived(info) => self.semantic_commit_derived(info),
            DeltaEvent::Evidence(rule) => self.semantic_commit_evidence(rule),
            DeltaEvent::Repr { key, name, info, monomorph, obligations } => {
                self.semantic_commit_repr(key, name, info, monomorph, obligations);
            }
            DeltaEvent::Impl { repr, op, entry, obligations } => {
                self.semantic_commit_impl(repr, op, entry, obligations);
            }
            DeltaEvent::Access { designed, minted } => self.designate_access(&designed, &minted),
            DeltaEvent::InternalAccess { minted, owner } => self.internal_access(&minted, &owner),
            DeltaEvent::Meta { module, name, slot, definition } => {
                self.semantic_commit_meta(module, name, slot, definition);
            }
        }
    }

    fn preflight_module_event(&self, event: &DeltaEvent) -> Result<(), ModuleReplayError> {
        let conflict = match event {
            DeltaEvent::Name { name, .. }
                if self.names.declares(&self.names.scope().module, name) => Some("name"),
            DeltaEvent::Global { abs, registration, .. }
                if self.names.global(&registration.key).is_some()
                    || self.names.global_name_at(*abs).is_some() => Some("global-name"),
            DeltaEvent::GenDef { key, abs }
                if self.types.gdefs().has_binding(key, *abs) => Some("generated-definition"),
            DeltaEvent::GenTyCode { tag, .. }
                if self.types.gdefs().has_ty_code(*tag) => Some("generated type-code"),
            DeltaEvent::GenTyCodeFn { tag, .. }
                if self.types.gdefs().has_ty_code_fn(*tag) => Some("generated type-code function"),
            DeltaEvent::GenWfSlots { tag, .. }
                if self.types.gdefs().has_wf_slot_entry(*tag) => Some("generated Wf-slot"),
            DeltaEvent::GenSpineCodes { tag, .. }
                if self.types.gdefs().has_spine_code_entry(*tag) => Some("generated spine-code"),
            DeltaEvent::GenFamLevels { tag, .. }
                if self.types.gdefs().has_fam_level_entry(*tag) => Some("generated family-level"),
            DeltaEvent::Inductive { module, info }
                if self.types.inductive(&crate::names::qkey(module, &info.name)).is_some()
                    || self.types.by_tag(info.tag).is_some()
                    || info.skel.as_ref().is_some_and(|skel| self.types.by_tag(skel.tag).is_some()) =>
            {
                Some("nominal-type")
            }
            DeltaEvent::Class { key, .. } if self.traits.has_class(key) => Some("class"),
            DeltaEvent::Instance { key, .. } if self.traits.has_instance(key) => Some("instance"),
            DeltaEvent::Designation { key, .. } if self.traits.designation(key).is_some() => {
                Some("designation")
            }
            DeltaEvent::Derived(info)
                if self.traits.derived().iter().any(|old| old.abs == info.abs) => Some("derived-instance"),
            DeltaEvent::Evidence(rule) if self.traits.has_evidence(&rule.global) => Some("evidence-rule"),
            DeltaEvent::Repr { key, name, monomorph, .. }
                if self.representations.for_spec(key).is_some()
                    || self.representations.has_name(name)
                    || monomorph.as_ref().is_some_and(|(tag, args)| {
                        self.representations.monomorph(*tag, args).is_some()
                    }) => Some("representation"),
            DeltaEvent::Impl { repr, op, .. }
                if self.representations.has_impl(repr, op) => Some("implementation"),
            DeltaEvent::Access { designed, .. }
                if self.access_alias(designed).is_some() => Some("designed-access"),
            DeltaEvent::Meta { module, name, slot, .. }
                if self.meta_programs.definition(module, name).is_some()
                    || slot.is_some_and(|slot| self.meta_programs.slot_owner(slot).is_some()) =>
            {
                Some("meta-program")
            }
            _ => None,
        };
        conflict.map_or(Ok(()), |registry| Err(ModuleReplayError::MetadataConflict(registry)))
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;
    use std::sync::Arc as Rc;

    use heather_kernel::term::{GlobalBinding, Term};

    use super::*;

    #[test]
    fn diagnostic_extraction_returns_a_delta_only_for_a_whole_successful_module() {
        let mut e = Elaborator::with_prelude().unwrap();
        let before = e.psi().bindings.len();
        let delta = e
            .check_module_delta(
                "good",
                "fn value() -> Nat { 0 }",
                ModuleDependencyIdentity::default(),
            )
            .unwrap();
        assert!(delta.binding_count() > 0);
        assert!(e.psi().bindings.len() > before);

        let after_good = e.psi().bindings.len();
        let errs = match e.check_module_delta(
            "mixed",
            "fn kept() -> Nat { 0 }\nfn broken() -> Nat { Type }",
            ModuleDependencyIdentity::default(),
        ) {
            Ok(_) => panic!("the broken module unexpectedly checked"),
            Err(errs) => errs,
        };
        assert_eq!(errs.len(), 1);
        assert!(
            e.psi().bindings.len() > after_good,
            "ordinary diagnostic recovery must retain the successful item"
        );
        assert!(e.module_journal.borrow().is_none());
    }

    #[test]
    fn a_clone_records_nothing_and_a_restore_cuts_the_journal_back() {
        // A probe clone must not copy the journal (that made every probe
        // linear in the module's events) nor record into one; a snapshot
        // restored over a declaration that failed after recording must leave
        // the live journal at the snapshot's lengths.
        let mut e = Elaborator::new();
        *e.module_journal.borrow_mut() = Some(ModuleJournal::new(0, 0));
        e.semantic_commit_name("before", NameKind::Global);
        let snapshot = e.clone();
        let mut probe = e.clone();
        assert!(probe.module_journal.borrow().is_none());
        probe.semantic_commit_name("probed", NameKind::Global);
        e.semantic_commit_name("failed", NameKind::Global);
        assert_eq!(e.module_journal.borrow().as_ref().unwrap().events.len(), 2);
        e.restore_from_clone(snapshot);
        let journal = e.module_journal.borrow();
        let events = &journal.as_ref().expect("the live journal survives a restore").events;
        assert!(matches!(events.as_slice(), [DeltaEvent::Name { name, .. }] if name == "before"));
    }

    #[test]
    fn elaborator_semantic_commits_route_through_this_module() {
        // A new declaration feature must not update a durable registry while
        // forgetting its ModuleDelta event. Runtime source inspection is
        // deliberate here: it covers newly added `src/**/*.rs` files without
        // maintaining a second module list, and fails the ordinary test rail.
        const BYPASSES: &[&str] = &[
            "self.names.insert_current(",
            "self.names.commit_global(",
            "self.provenance.commit(",
            "self.types.commit(",
            "self.types.gdefs_mut().insert_binding(",
            "self.types.gdefs_mut().insert_ty_code(",
            "self.types.gdefs_mut().insert_wf_slots(",
            "self.types.gdefs_mut().insert_spine_codes(",
            "self.types.gdefs_mut().insert_fam_levels(",
            "self.traits.commit_class(",
            "self.traits.commit_instance(",
            "self.traits.commit_designation(",
            "self.traits.commit_derived(",
            "self.representations.commit_repr(",
            "self.representations.commit_impl(",
            "self.meta_programs.commit(",
        ];

        fn inspect(dir: &Path, violations: &mut Vec<String>) {
            for entry in fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    inspect(&path, violations);
                } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs")
                    && path.file_name().and_then(|name| name.to_str()) != Some("module_delta.rs")
                {
                    let source = fs::read_to_string(&path).unwrap();
                    for bypass in BYPASSES {
                        if source.contains(bypass) {
                            violations.push(format!("{} contains `{bypass}`", path.display()));
                        }
                    }
                }
            }
        }

        let mut violations = Vec::new();
        // `../elab/src` rather than `src`: these tests compile as the
        // `heather-elab-unit` package (crates/elab-unit), whose manifest
        // directory is a sibling of this crate's.
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src");
        inspect(src.as_path(), &mut violations);
        assert!(
            violations.is_empty(),
            "semantic registry commits bypass ModuleDelta's centralized commit sink:\n{}",
            violations.join("\n")
        );
    }

    #[test]
    fn a_rejected_kernel_suffix_publishes_no_metadata_or_bindings() {
        let identity = ModuleDependencyIdentity::default();
        let mut source = Elaborator::new();
        let mut delta = source
            .elab_module_delta("bad", "fn value() -> Nat { 0 }", identity.clone())
            .unwrap();
        let GlobalBinding::Tm { body, .. } = delta.extension.last_mut().unwrap() else {
            panic!("ordinary function is a term binding");
        };
        *body = Some(Rc::new(Term::TmNat));

        let mut target = Elaborator::new();
        let before = target.psi().clone();
        assert!(matches!(
            target.replay_module_delta(&delta, &identity),
            Err(ModuleReplayError::Kernel(_))
        ));
        assert_eq!(target.psi(), &before);
        target
            .elab_module_source("bad", "fn value() -> Nat { 0 }")
            .expect("the rejected delta exposed neither its name nor its binding");
    }

    /// The recheck of a stored suffix runs its definition bodies on the
    /// kernel worker pool (`recheck_extension`); a module's answer never
    /// depends on the width (`docs/parallel-kernel-gate-design.md` §5.1), so
    /// the wide replay accepts what the serial one accepts, refuses what it
    /// refuses, and the kernel is what did the refusing at both widths.
    #[test]
    fn a_wide_replay_answers_as_the_serial_one_does() {
        let identity = ModuleDependencyIdentity::default();
        let module = "fn value() -> Nat { 0 }\nfn other() -> Nat { 1 }\n\
                      theorem value_is_zero(): value() = 0 { refl }";
        let mut source = Elaborator::new();
        let good = source.elab_module_delta("wide", module, identity.clone()).unwrap();
        let bodies = good
            .extension
            .iter()
            .filter(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }))
            .count();
        // The two functions carry bodies; a theorem is pushed opaque.
        assert!(bodies >= 2, "{bodies} definition bodies");

        for workers in [1, 8] {
            let mut target = Elaborator::new();
            target.set_kernel_workers(workers);
            let before = heather_kernel::stats::snapshot();
            target.replay_module_delta(&good, &identity).expect("the stored suffix rechecks");
            // Wide, one `check_term` per body, counted on this thread: the
            // workers' counters fold into it at the join. (The serial form is
            // one extension call, which the `check_terms` counter does not
            // see — it counts the `check_term` entry points only.)
            let checks = heather_kernel::stats::snapshot().since(&before).check_terms;
            if workers > 1 {
                assert!(checks >= bodies as u64, "width {workers}: {checks} checks for {bodies} bodies");
            }
            assert_eq!(target.psi(), source.psi());
        }

        // A body that does not inhabit its statement, behind two that do.
        let mut bad_body = good.clone();
        let last_body = bad_body
            .extension
            .iter()
            .rposition(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }))
            .unwrap();
        let GlobalBinding::Tm { body, .. } = &mut bad_body.extension[last_body] else {
            unreachable!()
        };
        *body = Some(Rc::new(Term::TmNat));
        // A statement that is not well-formed, ahead of bodies that are.
        let mut bad_statement = good.clone();
        let first_tm = bad_statement
            .extension
            .iter()
            .position(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }))
            .unwrap();
        let GlobalBinding::Tm { ty, .. } = &mut bad_statement.extension[first_tm] else {
            unreachable!()
        };
        // `Ty 0` lives at level 1; the binding says level 0.
        *ty = Rc::new(heather_kernel::term::Type::Ty(heather_kernel::level::Level::Zero));

        for delta in [&bad_body, &bad_statement] {
            let mut serial = Elaborator::new();
            serial.set_kernel_workers(1);
            let mut wide = Elaborator::new();
            wide.set_kernel_workers(8);
            let before = wide.psi().clone();
            let (s, w) = (
                serial.replay_module_delta(delta, &identity),
                wide.replay_module_delta(delta, &identity),
            );
            let (Err(ModuleReplayError::Kernel(s)), Err(ModuleReplayError::Kernel(w))) = (&s, &w)
            else {
                panic!("both widths refuse through the kernel: {s:?} / {w:?}")
            };
            assert_eq!(s, w, "the wide replay names the serial replay's error");
            assert_eq!(wide.psi(), &before, "nothing lands from a rejected replay");
        }
    }

    #[test]
    fn the_journal_records_non_kernel_semantic_registries() {
        let mut source = Elaborator::with_prelude().unwrap();
        let delta = source
            .elab_module_delta(
                "features",
                r#"
inductive Z { Z0 }
inductive Two { TA, TB(n: Nat) }
inductive Chain { End, Link(tail: Chain) }
fn zop(x: Z, y: Z) -> Z { x }
class Mag<A> { op: A -> A -> A }
instance Mag<Z> { op := zop }
designation + at Z := zop
meta fn zero_code(g: Ctx) -> Code(g |- Nat) { code { 0 } }
datarepr NatN for Nat := repr::naive();
"#,
                ModuleDependencyIdentity::default(),
            )
            .unwrap();

        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::GenDef { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::GenTyCode { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::GenWfSlots { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::GenSpineCodes { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::Inductive { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::Class { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::Instance { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::Designation { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::Meta { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::Repr { .. })));
        assert!(delta.events.iter().any(|event| matches!(event, DeltaEvent::Access { .. })));

        let mut replayed = Elaborator::with_prelude().unwrap();
        replayed
            .replay_module_delta(&delta, &ModuleDependencyIdentity::default())
            .unwrap();
        replayed
            .elab_module_source(
                "consumer",
                "import features;\nfn use_designation() -> Z { Z0 + Z0 }",
            )
            .expect("replayed designation and nominal names are observable downstream");
    }
}
