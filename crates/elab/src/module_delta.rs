//! Logical, representation-independent semantic additions made by one module.
//!
//! This is the in-memory precursor to the persistent module-image format. It
//! records operations at infallible commit points rather than diffing private
//! maps or serializing their current storage layout.

use std::fmt;
use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalCtx, Type};
use heather_kernel::typing::{self, TypeError};
use heather_syntax::OpFixity;

use crate::datarepr::{DatareprInfo, DatareprKey, ImplEntry, Obligation};
use crate::gendefs::{GenDef, WfSlots, SpineCodes};
use crate::inductive::Inductive;
use crate::metaprograms::MetaDef;
use crate::names::{GlobalRegistration, NameKind, Scope};
use crate::resolve::DerivedInst;
use crate::slots::Slot;
use crate::traits::{ClassInfo, DesignationInfo, InstanceInfo, InstKey};
use crate::{ElabError, Elaborator, R};

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
    pub(crate) scope: Scope,
    pub(crate) events: Vec<DeltaEvent>,
}

impl ModuleDelta {
    pub fn module(&self) -> &str {
        &self.module
    }

    pub fn binding_count(&self) -> usize {
        self.extension.len()
    }

    /// Encode this checked, process-local delta as a deterministic semantic
    /// module image. The dependency kernel prefix itself is deliberately not
    /// serialized; only its length and the loader-supplied interface
    /// identities enter the image.
    pub fn to_image_bytes(&self) -> Vec<u8> {
        crate::module_image::encode_delta(self)
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

#[derive(Debug)]
pub enum ModuleReplayError {
    DependencyIdentity,
    DependencyKernelPrefix,
    Kernel(TypeError),
    MetadataConflict(&'static str),
}

impl fmt::Display for ModuleReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DependencyIdentity => write!(f, "module dependency identity does not match"),
            Self::DependencyKernelPrefix => {
                write!(f, "module dependency kernel prefix does not match")
            }
            Self::Kernel(error) => write!(f, "stored module binding was rejected: {error:?}"),
            Self::MetadataConflict(registry) => {
                write!(f, "stored module metadata conflicts with the accepted {registry} registry")
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
    GenTyCode {
        tag: u32,
        inline: Rc<Type>,
        level: Level,
    },
    GenWfSlots {
        tag: u32,
        slots: WfSlots,
    },
    GenSpineCodes {
        tag: u32,
        codes: SpineCodes,
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
    ) {
        self.record_module_event(|| DeltaEvent::GenTyCode {
            tag,
            inline: Rc::clone(&inline),
            level: level.clone(),
        });
        self.types.gdefs_mut().insert_ty_code(tag, (inline, level));
    }

    pub(crate) fn semantic_commit_gen_wf_slots(&mut self, tag: u32, slots: WfSlots) {
        self.record_module_event(|| DeltaEvent::GenWfSlots {
            tag,
            slots: slots.clone(),
        });
        self.types.gdefs_mut().insert_wf_slots(tag, slots);
    }

    pub(crate) fn semantic_commit_gen_spine_codes(&mut self, tag: u32, codes: SpineCodes) {
        self.record_module_event(|| DeltaEvent::GenSpineCodes {
            tag,
            codes: codes.clone(),
        });
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
        *self.module_journal.borrow_mut() = Some(ModuleJournal { events: Vec::new() });
        let result = self.session_transaction(|me| me.elab_module_source(module, src));
        let journal = self
            .module_journal
            .borrow_mut()
            .take()
            .expect("module journal was installed");
        result?;
        let extension = self.psi.bindings.iter().skip(base_len).cloned().collect();
        Ok(ModuleDelta {
            module: module.to_string(),
            dependencies,
            dependency_psi,
            extension,
            scope: self.names.scope().clone(),
            events: journal.events,
        })
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
        *self.module_journal.borrow_mut() = Some(ModuleJournal { events: Vec::new() });
        let errs = self.check_module_source_inner(module, src);
        let journal = self
            .module_journal
            .borrow_mut()
            .take()
            .expect("module journal was installed");
        if !errs.is_empty() {
            return Err(errs);
        }
        let extension = self.psi.bindings.iter().skip(base_len).cloned().collect();
        Ok(ModuleDelta {
            module: module.to_string(),
            dependencies,
            dependency_psi,
            extension,
            scope: self.names.scope().clone(),
            events: journal.events,
        })
    }

    /// Recheck the stored suffix, install metadata into a private candidate,
    /// and publish the candidate only after every operation succeeds.
    pub fn replay_module_delta(
        &mut self,
        delta: &ModuleDelta,
        dependencies: &ModuleDependencyIdentity,
    ) -> Result<(), ModuleReplayError> {
        if dependencies != &delta.dependencies {
            return Err(ModuleReplayError::DependencyIdentity);
        }
        if self.psi.bindings.iter().ne(delta.dependency_psi.bindings.iter()) {
            return Err(ModuleReplayError::DependencyKernelPrefix);
        }
        typing::check_global_ctx_extension(&self.psi, &delta.extension, 0, self.fuel)
            .map_err(ModuleReplayError::Kernel)?;

        let mut candidate = self.semantic_image().elaborator();
        candidate.names.enter_scope(delta.scope.clone());
        candidate.psi.extend(delta.extension.iter().cloned());
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
        Ok(())
    }

    fn apply_module_event(&mut self, event: DeltaEvent) {
        match event {
            DeltaEvent::Name { name, kind } => self.semantic_commit_name(&name, kind),
            DeltaEvent::Global { abs, registration, is_axiom, direct_dependencies } => {
                self.semantic_commit_global(abs, registration, is_axiom, direct_dependencies);
            }
            DeltaEvent::GenDef { key, abs } => self.semantic_commit_gen_def(key, abs),
            DeltaEvent::GenTyCode { tag, inline, level } => {
                self.semantic_commit_gen_ty_code(tag, inline, level);
            }
            DeltaEvent::GenWfSlots { tag, slots } => {
                self.semantic_commit_gen_wf_slots(tag, slots);
            }
            DeltaEvent::GenSpineCodes { tag, codes } => {
                self.semantic_commit_gen_spine_codes(tag, codes);
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
    use std::rc::Rc;

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
        inspect(Path::new(env!("CARGO_MANIFEST_DIR")).join("src").as_path(), &mut violations);
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
