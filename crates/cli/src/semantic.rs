//! Cache-aware semantic module loading without presentation policy.
//!
//! A session follows one topologically ordered import closure. It owns the
//! exact-prefix identity required by the current absolute-Ψ image format and
//! returns diagnostics, warnings and cache notices to its caller. Cache hits
//! are always bounded, kernel-checked semantic replay; this component never
//! installs the separate trusted declaration cache gate.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::io::Write as _;
use std::ops::Range;
use std::path::PathBuf;
use std::sync::OnceLock;

use heather_cache::merkle::{self, Hash};
use heather_cache::module_image::{
    ImageFreshness, ImageRefusal, ModuleCacheKey, ModuleImageCache, SemanticsIdentity, SourceKey,
    WorldRecord, WorldReference,
};
use heather_cache::sha256::Sha256;
use heather_elab::{
    ElabError, Elaborator, LintProfile, ModuleDelta, ModuleDependencyIdentity, NameWorld,
    RegistryPart, RelocationTarget, Warning, WorldHasher, source_identifiers, stats,
};
use heather_kernel::term::{Term, Type};

use crate::loader::Module;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheNoticeKind {
    LoadRejected,
    ReplayRejected,
    PublishFailed,
    /// An image another build wrote was replayed under
    /// [`ImageFreshness::AcceptStale`]. Kernel-rechecked like any replay; the
    /// notice exists because the current frontend was not exercised on it.
    StaleReplayed,
    /// The module's previous image (for slice replay after an edit) could
    /// not be loaded; the module is elaborated in full.
    PreviousUnusable,
    /// The module was not elaborated: an image of the same source over
    /// another dependency world was moved onto this one, because nothing it
    /// observed changed (`docs/module-interface-cutoff-design.md`), and
    /// replayed like any image. Only under [`ImageFreshness::AcceptStale`];
    /// also reported when such an image is replayed later.
    Relocated,
    /// A relocated image failed its replay; the module is elaborated.
    RelocationRejected,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CacheNotice {
    pub module: String,
    pub kind: CacheNoticeKind,
    pub error: String,
}

impl fmt::Display for CacheNotice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            CacheNoticeKind::LoadRejected => write!(
                f,
                "cache: stored module `{}` is unusable ({}) — rebuilding",
                self.module, self.error
            ),
            CacheNoticeKind::ReplayRejected => write!(
                f,
                "cache: stored module `{}` failed semantic replay ({}) — rebuilding",
                self.module, self.error
            ),
            CacheNoticeKind::PublishFailed => {
                write!(f, "cache: could not store module `{}` ({})", self.module, self.error)
            }
            CacheNoticeKind::PreviousUnusable => write!(
                f,
                "cache: the previous image of module `{}` is unusable ({}) — elaborating every declaration",
                self.module, self.error
            ),
            CacheNoticeKind::Relocated => write!(
                f,
                "cache: module `{}` moved from an image of the same source over another dependency world ({}), kernel-rechecked or vouched for by the verdict store; a run without stale images re-elaborates it",
                self.module, self.error
            ),
            CacheNoticeKind::RelocationRejected => write!(
                f,
                "cache: the image of module `{}` moved from another dependency world failed replay ({}) — rebuilding",
                self.module, self.error
            ),
            CacheNoticeKind::StaleReplayed => write!(
                f,
                "cache: module `{}` replayed from an image of another build ({}), kernel-rechecked or vouched for by the verdict store; a run without stale images re-elaborates it",
                self.module, self.error
            ),
        }
    }
}

pub struct ModuleOutcome {
    pub errors: Vec<ElabError>,
    pub warnings: Vec<Warning>,
    pub replayed: bool,
    /// Declarations reproduced from the module's previous image after an
    /// edit (`docs/declaration-slice-replay-design.md`); zero when the
    /// module replayed whole or was elaborated from scratch.
    pub replayed_items: usize,
    /// Declarations elaborated because `--only` named them
    /// (`docs/check-only-design.md`); such a module is not published.
    pub forced_items: usize,
    pub notices: Vec<CacheNotice>,
}

/// One module of the session's world, in load order: what relocating a later
/// module needs to know about it (`docs/module-interface-cutoff-design.md`).
struct WorldModule {
    name: String,
    /// Its Ψ positions.
    range: Range<usize>,
    /// Its registry contribution; `None` for the bindings that were in Ψ
    /// before the session's first module (the prelude), which stand in the
    /// registry digest by their content hashes alone.
    registry: Option<RegistryPart>,
    /// The digest of [`Self::registry`]'s projection, once taken. `None`
    /// inside when it could not be (an unhashable binding).
    digest: OnceLock<Option<Hash>>,
    /// Content hash → its positions in this module, ascending: how a
    /// reference is found again after the module's bindings moved.
    index: OnceLock<HashMap<Hash, Vec<usize>>>,
}

/// What the world under a module offers its elaboration, beyond the
/// bindings it refers to: the registry digest, and the names, from which
/// the digest of what the module's identifiers and lookups resolve to is
/// taken once the lookups are known.
struct WorldView {
    registry: Hash,
    names: NameWorld,
    identifiers: BTreeSet<String>,
}

/// The outcome of looking for an image of the same source to move.
enum Relocation {
    NoCandidate,
    Refused(String),
    Moved { delta: ModuleDelta, warnings: Vec<Warning>, lookups: Vec<String> },
}

struct MerkleHasher<'a>(&'a [Option<Hash>]);

impl WorldHasher for MerkleHasher<'_> {
    fn binding(&mut self, abs: usize) -> Option<[u8; 32]> {
        *self.0.get(abs)?
    }

    fn ty(&mut self, scope: usize, t: &Type) -> Option<[u8; 32]> {
        merkle::type_hash(self.0, u32::try_from(scope).ok()?, t)
    }

    fn tm(&mut self, scope: usize, t: &Term) -> Option<[u8; 32]> {
        merkle::term_hash(self.0, u32::try_from(scope).ok()?, t)
    }
}

const BASE_MODULE: &str = "<base>";

/// State for one accepted, topologically ordered module closure.
pub struct SemanticSession {
    images: Option<ModuleImageCache>,
    interfaces: Vec<[u8; 32]>,
    images_usable: bool,
    freshness: ImageFreshness,
    hits: usize,
    stale_hits: usize,
    relocated: usize,
    replayed_items: usize,
    /// The modules checked so far, after the bindings that were in Ψ before
    /// the first: the dependency world of the next one.
    world: Vec<WorldModule>,
    /// Content hash per Ψ binding (`merkle::interface_hash`), synced lazily:
    /// only a miss needs it.
    merkle: Vec<Option<Hash>>,
    /// `HEATHER_RELOCATION_AUDIT`: under [`ImageFreshness::Exact`], every
    /// module elaborated after a miss is also moved from a candidate image
    /// when one passes, and the two are compared, one line per module
    /// appended here (`docs/module-interface-cutoff-design.md` §5).
    audit: Option<PathBuf>,
    /// `--only`: per module, the declarations to elaborate from source over
    /// a replayed prefix. A module named here is loaded from its previous
    /// image and never published.
    only: BTreeMap<String, BTreeSet<String>>,
    /// The `--only` names the passes met, `module::name`.
    only_met: BTreeSet<String>,
}

/// `--only` asked for a module's previous image and there was none: the
/// prefix a probe replays has to have been checked and published once.
///
/// There are two ways to get here and the message says both, because one of
/// them makes the obvious advice unfollowable: a module whose image the store
/// refused — over the decode budget — is checked and re-elaborated on every
/// warm run, so `heather check --cache` succeeds and still leaves nothing to
/// replay (`issues/check-only-no-stored-image.md`).
///
/// Since 2026-09-20 the store leaves a marker when it declines an image, so
/// the two ways are usually *told apart* rather than merely both named:
/// `refusal` is `Some` exactly when this world's last publish was refused on
/// size, and then the message quotes the size and stops advising a re-run
/// that cannot work.
#[derive(Debug)]
pub struct NoPreviousImage {
    pub module: String,
    pub refusal: Option<ImageRefusal>,
}

impl fmt::Display for NoPreviousImage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.refusal {
            Some(refusal) => write!(
                f,
                "--only: module `{}` has no stored image to replay the prefix from because the \
                 store refused it: {}. It was checked; re-running `heather check --cache` will \
                 not help, because the refusal is the image's size and not a missing run. A \
                 module whose image does not fit cannot be probed with --only at all",
                self.module, refusal
            ),
            None => write!(
                f,
                "--only: no stored image of module `{}` over these dependencies to replay the \
                 prefix from. Either it has not been checked with `--cache` over these \
                 dependencies yet — run `heather check --cache` on the file once first — or its \
                 image was refused as too large to store, which that run reports as `cache: could \
                 not store module `{}``; a module whose image does not fit cannot be probed with \
                 --only at all",
                self.module, self.module
            ),
        }
    }
}

impl SemanticSession {
    pub fn new(cache_dir: Option<PathBuf>) -> Self {
        let images = cache_dir.map(ModuleImageCache::new);
        Self {
            images_usable: images.is_some(),
            images,
            interfaces: Vec::new(),
            freshness: ImageFreshness::Exact,
            hits: 0,
            stale_hits: 0,
            relocated: 0,
            replayed_items: 0,
            world: Vec::new(),
            merkle: Vec::new(),
            audit: std::env::var_os("HEATHER_RELOCATION_AUDIT").map(PathBuf::from),
            only: BTreeMap::new(),
            only_met: BTreeSet::new(),
        }
    }

    /// `--only`: per module, the declarations to elaborate from source
    /// while the rest of the module replays (`docs/check-only-design.md`).
    pub fn with_only(mut self, only: BTreeMap<String, BTreeSet<String>>) -> Self {
        self.only = only;
        self
    }

    /// The `--only` names (`module::name`) no pass met — the ones to report
    /// as unknown once every module has been checked.
    pub fn only_unmet(&self) -> Vec<String> {
        self.only
            .iter()
            .flat_map(|(module, names)| names.iter().map(move |n| format!("{module}::{n}")))
            .filter(|full| !self.only_met.contains(full))
            .collect()
    }

    /// Append the exact lane's relocation audit to `path` instead of where
    /// `HEATHER_RELOCATION_AUDIT` points (`None`: no audit).
    pub fn with_audit(mut self, path: Option<PathBuf>) -> Self {
        self.audit = path;
        self
    }

    /// Choose how images written by other builds are treated. The default
    /// is [`ImageFreshness::Exact`]; a final verification must keep it.
    pub fn with_freshness(mut self, freshness: ImageFreshness) -> Self {
        self.freshness = freshness;
        self
    }

    pub fn freshness(&self) -> ImageFreshness {
        self.freshness
    }

    /// Modules replayed from images, stale ones included.
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Modules replayed from images another build wrote.
    pub fn stale_hits(&self) -> usize {
        self.stale_hits
    }

    /// Modules moved from an image of the same source over another
    /// dependency world, counted in [`Self::hits`] too.
    pub fn relocated(&self) -> usize {
        self.relocated
    }

    /// Declarations reproduced from previous images after edits, summed
    /// over the session's modules.
    pub fn replayed_items(&self) -> usize {
        self.replayed_items
    }

    /// Check or replay the next module. After a source error, later modules
    /// remain checkable for diagnostic recovery, but no longer read or write
    /// images because the accepted prefix has been broken.
    pub fn check(
        &mut self,
        elab: &mut Elaborator,
        module: &Module,
        lint_profile: LintProfile,
    ) -> ModuleOutcome {
        // One module scope, so the dump has a per-module row whose total covers
        // the declarations inside it plus the module-level work — parse,
        // imports, decode, replay, publication
        // (`docs/instrumentation-design.md` §3).
        let _module = stats::scope(stats::ScopeKind::Module, &module.name, "");
        if !self.images_usable {
            return ModuleOutcome {
                errors: elab.check_module_source(&module.name, &module.src),
                warnings: elab.take_warnings(),
                replayed: false,
                replayed_items: 0,
                forced_items: 0,
                notices: Vec::new(),
            };
        }

        let start = elab.psi().bindings.len();
        if self.world.is_empty() && start > 0 {
            self.world.push(WorldModule::new(BASE_MODULE.into(), 0..start, None));
        }
        let dependencies = ModuleDependencyIdentity::new(self.interfaces.clone());
        let key = ModuleCacheKey::for_source(
            &module.name,
            &module.src,
            &dependencies,
            lint_profile,
        );
        let source = SourceKey::for_source(&module.name, &module.src, lint_profile);
        let mut notices = Vec::new();
        if let Some(force) = self.only.get(&module.name).cloned() {
            let outcome = self.check_only(elab, module, dependencies, force, notices);
            if outcome.errors.is_empty() {
                self.enter_world(elab, module, start, None);
            }
            return outcome;
        }
        let images = self.images.as_ref().expect("usable images have a cache");
        // A miss takes the key's build lock and looks again before building:
        // another process missing the same key at the same moment (the suite
        // starts its targets together on an empty or newly stale store) has
        // usually just published it, and replaying beats elaborating twice.
        // Held until this function returns, i.e. past the publication below.
        // A hit never takes it, so concurrent replays stay concurrent.
        let mut build_lock = None;
        loop {
            // The three phases warm replay is made of — read/checksum/decode,
            // the kernel recheck of the decoded delta, and publication (render
            // plus hash). The fast lane's premise rests on these
            // (`issues/semantic-replay-phase-attribution.md`).
            let decoded = stats::timed(stats::Timer::ImageDecode, || {
                images.load(key, elab.psi().clone(), module.src.len(), self.freshness)
            });
            match decoded {
                Ok(Some(loaded)) => match stats::timed(stats::Timer::ImageRecheck, || {
                    elab.replay_module_delta(&loaded.delta, &dependencies)
                }) {
                    Ok(()) => {
                        self.interfaces.push(loaded.interface_hash);
                        self.hits += 1;
                        match loaded.stale {
                            Some(writer) if writer == SemanticsIdentity::relocated() => {
                                self.relocated += 1;
                                notices.push(CacheNotice {
                                    module: module.name.clone(),
                                    kind: CacheNoticeKind::Relocated,
                                    error: "stored after an earlier relocation".into(),
                                });
                            }
                            Some(writer) => {
                                self.stale_hits += 1;
                                notices.push(CacheNotice {
                                    module: module.name.clone(),
                                    kind: CacheNoticeKind::StaleReplayed,
                                    error: format!(
                                        "build {} rather than {}",
                                        writer.short(),
                                        SemanticsIdentity::current().short()
                                    ),
                                });
                            }
                            None => {}
                        }
                        self.enter_world(elab, module, start, Some(loaded.delta.registry_part()));
                        return ModuleOutcome {
                            errors: Vec::new(),
                            warnings: loaded.warnings,
                            replayed: true,
                            replayed_items: 0,
                            forced_items: 0,
                            notices,
                        };
                    }
                    // A dependency theorem this module computed with has a
                    // new proof under the same statement: an ordinary miss,
                    // which the slice path below turns into re-checking just
                    // the declarations that opened it
                    // (`issues/theorem-witness-unfolding.md`).
                    Err(heather_elab::ModuleReplayError::OpenedProofChanged) => {}
                    Err(error) => notices.push(CacheNotice {
                        module: module.name.clone(),
                        kind: CacheNoticeKind::ReplayRejected,
                        error: error.to_string(),
                    }),
                },
                Ok(None) if build_lock.is_none() => {
                    if let Some(lock) = images.build_lock(key) {
                        build_lock = Some(lock);
                        continue;
                    }
                }
                Ok(None) => {}
                Err(error) => notices.push(CacheNotice {
                    module: module.name.clone(),
                    kind: CacheNoticeKind::LoadRejected,
                    error: error.to_string(),
                }),
            }
            break;
        }

        // A miss. What the world under the module offers it, for moving an
        // image of the same source here (the stale lane) or auditing that
        // move against the elaboration (the exact lane), and for the world
        // record the publication below carries either way.
        let view = stats::timed(stats::Timer::ImageRelocate, || self.observe_world(elab, module));
        if view.is_none() && std::env::var_os("HEATHER_RELOCATION_DEBUG").is_some() {
            eprintln!("relocation-debug {}: no world view", module.name);
        }
        let mut audited = None;
        if let Some(view) = &view {
            match self.freshness {
                ImageFreshness::AcceptStale => {
                    match stats::timed(stats::Timer::ImageRelocate, || {
                        self.relocation(elab, module, source, &dependencies, view)
                    }) {
                        Relocation::Moved { delta, warnings, lookups } => match stats::timed(stats::Timer::ImageRecheck, || {
                            elab.replay_module_delta(&delta, &dependencies)
                        }) {
                            Ok(()) => {
                                self.interfaces.push(ModuleImageCache::interface_hash(&delta));
                                self.hits += 1;
                                self.relocated += 1;
                                notices.push(CacheNotice {
                                    module: module.name.clone(),
                                    kind: CacheNoticeKind::Relocated,
                                    error: "registries and the names it wrote unchanged".into(),
                                });
                                let record = self.world_record(start, &delta, view, lookups);
                                let images = self.images.as_ref().expect("usable images have a cache");
                                if let Err(error) = stats::timed(stats::Timer::ImagePublish, || {
                                    images.publish_world(
                                        key,
                                        &delta,
                                        &warnings,
                                        SemanticsIdentity::relocated(),
                                        record.as_ref().map(|r| (source, r)),
                                    )
                                }) {
                                    notices.push(CacheNotice {
                                        module: module.name.clone(),
                                        kind: CacheNoticeKind::PublishFailed,
                                        error: error.to_string(),
                                    });
                                }
                                self.enter_world(elab, module, start, Some(delta.registry_part()));
                                return ModuleOutcome {
                                    errors: Vec::new(),
                                    warnings,
                                    replayed: true,
                                    replayed_items: 0,
                                    forced_items: 0,
                                    notices,
                                };
                            }
                            Err(error) => notices.push(CacheNotice {
                                module: module.name.clone(),
                                kind: CacheNoticeKind::RelocationRejected,
                                error: error.to_string(),
                            }),
                        },
                        Relocation::NoCandidate => {}
                        Relocation::Refused(why) => {
                            if std::env::var_os("HEATHER_RELOCATION_DEBUG").is_some() {
                                eprintln!("relocation-debug {}: refused: {why}", module.name);
                            }
                        }
                    }
                }
                ImageFreshness::Exact if self.audit.is_some() => {
                    audited = Some(self.relocation(elab, module, source, &dependencies, view));
                }
                ImageFreshness::Exact => {}
            }
        }
        let images = self.images.as_ref().expect("usable images have a cache");

        // A source miss with a previous image of this module over the same
        // dependencies: the unchanged declarations are reproduced from its
        // slices and the rest elaborated
        // (`docs/declaration-slice-replay-design.md` §4). An unusable
        // previous image is reported and the module elaborated as usual.
        // Its decode is a decode: the previous image is the module's own,
        // often the largest in the closure, and the dashboard reads the
        // column (`issues/semantic-replay-phase-attribution.md`).
        let previous = match stats::timed(stats::Timer::ImageDecode, || {
            images.load_previous(&module.name, &dependencies, elab.psi().clone(), self.freshness)
        }) {
            Ok(previous) => previous,
            Err(error) => {
                notices.push(CacheNotice {
                    module: module.name.clone(),
                    kind: CacheNoticeKind::PreviousUnusable,
                    error: error.to_string(),
                });
                None
            }
        };
        // What the elaboration looks up by name beyond what the source
        // spells goes into the world record; declarations reproduced from the
        // previous image looked up what that image's record says they did.
        heather_elab::record_name_lookups();
        let checked = match &previous {
            Some(previous) => elab
                .check_module_delta_from(&module.name, &module.src, dependencies, &previous.delta)
                .map(|(delta, report)| (delta, report.replayed)),
            None => elab
                .check_module_delta(&module.name, &module.src, dependencies)
                .map(|delta| (delta, 0)),
        };
        let looked_up = heather_elab::take_name_lookups().unwrap_or_default();
        let lookups = match &previous {
            Some(previous) => previous.world.as_ref().map(|w| w.lookups.iter().cloned().collect::<BTreeSet<_>>()),
            None => Some(BTreeSet::new()),
        }
        .map(|mut lookups| {
            lookups.extend(looked_up);
            let identifiers = source_identifiers(&module.src);
            lookups.into_iter().filter(|l| !identifiers.contains(l)).collect::<Vec<_>>()
        });
        let (delta, replayed_items) = match checked {
            Ok(checked) => {
                // Drained, not printed: where an `omega` invocation's time went
                // is the dump's `omega_*` columns now, attributed by
                // declaration rather than by invocation
                // (`docs/instrumentation-design.md` §4). The per-invocation
                // reports stay available through `take_omega_reports`.
                elab.take_omega_reports();
                checked
            }
            Err(errors) => {
                self.images_usable = false;
                return ModuleOutcome {
                    errors,
                    warnings: elab.take_warnings(),
                    replayed: false,
                    replayed_items: 0,
                    forced_items: 0,
                    notices,
                };
            }
        };
        self.replayed_items += replayed_items;
        self.interfaces.push(ModuleImageCache::interface_hash(&delta));
        let warnings = elab.take_warnings();
        if let Some(audited) = audited {
            self.audit(&module.name, audited, &delta);
        }
        let record = view.zip(lookups).and_then(|(view, lookups)| {
            stats::timed(stats::Timer::ImageRelocate, || self.world_record(start, &delta, &view, lookups))
        });
        let images = self.images.as_ref().expect("usable images have a cache");
        if let Err(error) = stats::timed(stats::Timer::ImagePublish, || {
            images.publish_world(
                key,
                &delta,
                &warnings,
                SemanticsIdentity::current(),
                record.as_ref().map(|r| (source, r)),
            )
        }) {
            notices.push(CacheNotice {
                module: module.name.clone(),
                kind: CacheNoticeKind::PublishFailed,
                error: error.to_string(),
            });
        }
        self.enter_world(elab, module, start, Some(delta.registry_part()));
        ModuleOutcome { errors: Vec::new(), warnings, replayed: false, replayed_items, forced_items: 0, notices }
    }

    /// Record a module that is now in Ψ as part of the world under the next.
    fn enter_world(&mut self, elab: &Elaborator, module: &Module, start: usize, registry: Option<RegistryPart>) {
        let end = elab.psi().bindings.len();
        // `--only` keeps no delta to take a registry part from; a module of
        // unknown registry contribution makes every later digest
        // incomparable, which refuses every later relocation, as it should.
        let registry = registry.or_else(|| Some(RegistryPart::unknown()));
        self.world.push(WorldModule::new(module.name.clone(), start..end, registry));
    }

    /// Content hashes for every binding in Ψ, extending the ones already
    /// taken: Ψ only grows within a session.
    /// An assumption hashes in its own domain, as in the verdict store: a
    /// theorem turned into an assumption of the same statement is a change.
    fn sync_merkle(&mut self, elab: &Elaborator) {
        let psi = elab.psi();
        if self.merkle.len() > psi.bindings.len() {
            self.merkle.clear();
        }
        while self.merkle.len() < psi.bindings.len() {
            let at = self.merkle.len();
            let h = if elab.is_assumption_at(at) {
                merkle::assumption_interface_hash(&self.merkle, &psi.bindings[at])
            } else {
                merkle::interface_hash(&self.merkle, &psi.bindings[at])
            };
            self.merkle.push(h);
        }
    }

    /// The registry digest and name digest of the world under `module`
    /// (`docs/module-interface-cutoff-design.md` §2); `None` when some part
    /// of it cannot be hashed, which only ever costs a relocation.
    fn observe_world(&mut self, elab: &Elaborator, module: &Module) -> Option<WorldView> {
        self.sync_merkle(elab);
        let mut registry = Sha256::new();
        registry.update(b"heather/world-registry/1\0");
        for m in &self.world {
            match &m.registry {
                None => {
                    put_str(&mut registry, &m.name);
                    for at in m.range.clone() {
                        registry.update(&self.merkle[at]?);
                    }
                }
                Some(part) if part.is_inert() => {}
                Some(_) => {
                    put_str(&mut registry, &m.name);
                    registry.update(&m.registry_digest(&self.merkle)?);
                }
            }
        }
        Some(WorldView {
            registry: registry.finish(),
            names: elab.name_world(),
            identifiers: source_identifiers(&module.src),
        })
    }

    /// The digest of what the identifiers of `view` and `lookups` resolve to
    /// in its names: every declaration whose last segment is one of them,
    /// with its content hash, and every module named by one.
    fn names_digest(&self, view: &WorldView, lookups: &[String]) -> Option<Hash> {
        let lookups: BTreeSet<&str> = lookups.iter().map(String::as_str).collect();
        let wanted = |name: &str| view.identifiers.contains(name) || lookups.contains(name);
        let observed = view.names.observations(&wanted);
        let mut names = Sha256::new();
        names.update(b"heather/world-names/2\0");
        names.update(&(observed.bytes.len() as u64).to_le_bytes());
        names.update(&observed.bytes);
        for at in observed.globals {
            names.update(&(*self.merkle.get(at)?)?);
        }
        // A module name it wrote or looked up is a qualifier it may have
        // resolved.
        for m in &self.world {
            if wanted(&m.name) {
                put_str(&mut names, &m.name);
            }
        }
        Some(names.finish())
    }

    /// The world record a published image of `delta` carries: its
    /// dependency references by content, and the digests of `view`.
    fn world_record(&self, base: usize, delta: &ModuleDelta, view: &WorldView, lookups: Vec<String>) -> Option<WorldRecord> {
        let mut references = Vec::new();
        let refs = match delta.dependency_references() {
            Ok(refs) => refs,
            Err(e) => {
                if std::env::var_os("HEATHER_RELOCATION_DEBUG").is_some() {
                    eprintln!("relocation-debug {}: no record: {e}", delta.module());
                }
                return None;
            }
        };
        for at in refs {
            let module = self.world.partition_point(|m| m.range.end <= at);
            let m = self.world.get(module).filter(|m| m.range.contains(&at))?;
            let hash = (*self.merkle.get(at)?)?;
            let same = m.index(&self.merkle).get(&hash)?;
            references.push(WorldReference {
                abs: at as u64,
                module: module as u32,
                hash,
                rank: same.binary_search(&at).ok()? as u32,
                count: same.len() as u32,
            });
        }
        Some(WorldRecord {
            base: base as u64,
            modules: self.world.iter().map(|m| m.name.clone()).collect(),
            references,
            registry: view.registry,
            names: self.names_digest(view, &lookups)?,
            lookups,
        })
    }

    /// Look for an image of this exact source over another world, and move
    /// it onto this one if nothing it observed differs: the world's
    /// registries and what its identifiers resolve to are unchanged, and
    /// every binding it refers to is found again, by content, in the module
    /// it came from (`docs/module-interface-cutoff-design.md` §3). The moved
    /// delta is not replayed here.
    fn relocation(
        &self,
        elab: &Elaborator,
        module: &Module,
        source: SourceKey,
        dependencies: &ModuleDependencyIdentity,
        view: &WorldView,
    ) -> Relocation {
        let images = self.images.as_ref().expect("usable images have a cache");
        let loaded = match stats::timed(stats::Timer::ImageDecode, || {
            images.load_candidate(source, module.src.len(), self.freshness)
        }) {
            Ok(Some(loaded)) => loaded,
            Ok(None) => return Relocation::NoCandidate,
            Err(error) => return Relocation::Refused(format!("candidate unusable: {error}")),
        };
        let Some(record) = &loaded.world else {
            return Relocation::NoCandidate;
        };
        if record.registry != view.registry {
            return Relocation::Refused("the world's registries differ".into());
        }
        if Some(record.names) != self.names_digest(view, &record.lookups) {
            return Relocation::Refused("a name the module wrote resolves differently".into());
        }
        let by_name: HashMap<&str, &WorldModule> = self.world.iter().map(|m| (m.name.as_str(), m)).collect();
        let mut map = HashMap::with_capacity(record.references.len());
        for r in &record.references {
            let Some(m) = by_name.get(record.modules[r.module as usize].as_str()) else {
                return Relocation::Refused(format!("module `{}` is not in this world", record.modules[r.module as usize]));
            };
            match m.index(&self.merkle).get(&r.hash) {
                Some(same) if same.len() == r.count as usize => {
                    map.insert(r.abs as usize, same[r.rank as usize]);
                }
                _ => {
                    return Relocation::Refused(format!(
                        "a binding of `{}` the module refers to changed",
                        m.name
                    ));
                }
            }
        }
        match loaded.delta.relocate(RelocationTarget {
            dependency_psi: elab.psi().clone(),
            dependencies: dependencies.clone(),
            map: &mut |at| map.get(&at).copied(),
        }) {
            Ok(delta) => Relocation::Moved { delta, warnings: loaded.warnings, lookups: record.lookups.clone() },
            Err(refusal) => Relocation::Refused(refusal.to_string()),
        }
    }

    /// The exact lane's audit: compare what the stale lane would have moved
    /// here with what the elaborator just produced, and append the verdict
    /// (`docs/module-interface-cutoff-design.md` §5). `diverged` names a
    /// module whose relocation the digests let through and whose
    /// interface the elaboration does not reproduce: the cutoff lied.
    fn audit(&self, module: &str, attempt: Relocation, fresh: &ModuleDelta) {
        let (verdict, detail) = match attempt {
            Relocation::NoCandidate => return,
            Relocation::Refused(why) => ("refused", why),
            Relocation::Moved { delta, .. } => {
                if ModuleImageCache::interface_hash(&delta) != ModuleImageCache::interface_hash(fresh) {
                    ("diverged", "interface differs".to_string())
                } else if delta.to_image_bytes() != fresh.to_image_bytes() {
                    if std::env::var_os("HEATHER_RELOCATION_DEBUG").is_some() {
                        if let Some(path) = &self.audit {
                            let _ = std::fs::write(path.with_extension(format!("{module}.moved")), delta.to_image_bytes());
                            let _ = std::fs::write(path.with_extension(format!("{module}.fresh")), fresh.to_image_bytes());
                        }
                    }
                    ("same-interface", "image bytes differ".to_string())
                } else {
                    ("same", String::new())
                }
            }
        };
        let Some(path) = &self.audit else { return };
        let line = format!("{module}\t{verdict}\t{detail}\n");
        if let Ok(mut file) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
            let _ = file.write_all(line.as_bytes());
        }
    }

    /// The `--only` path for a module with named declarations: the module's
    /// previous image over the current dependency world is the prefix, the
    /// named items elaborate from source, and nothing is published
    /// (`docs/check-only-design.md` §2). The source-keyed image is not
    /// consulted — a hit would replay the whole module and elaborate nothing.
    fn check_only(
        &mut self,
        elab: &mut Elaborator,
        module: &Module,
        dependencies: ModuleDependencyIdentity,
        force: BTreeSet<String>,
        mut notices: Vec<CacheNotice>,
    ) -> ModuleOutcome {
        let images = self.images.as_ref().expect("usable images have a cache");
        let previous = stats::timed(stats::Timer::ImageDecode, || {
            images.load_previous(&module.name, &dependencies, elab.psi().clone(), self.freshness)
        });
        let previous = match previous {
            Ok(Some(previous)) => previous,
            Ok(None) => {
                self.images_usable = false;
                return ModuleOutcome {
                    errors: vec![ElabError::Elab {
                        msg: NoPreviousImage {
                            module: module.name.clone(),
                            refusal: images.refusal(&module.name, &dependencies),
                        }
                        .to_string(),
                        span: heather_syntax::Span { start: 0, end: 0 },
                    }],
                    warnings: Vec::new(),
                    replayed: false,
                    replayed_items: 0,
                    forced_items: 0,
                    notices,
                };
            }
            Err(error) => {
                notices.push(CacheNotice {
                    module: module.name.clone(),
                    kind: CacheNoticeKind::PreviousUnusable,
                    error: error.to_string(),
                });
                self.images_usable = false;
                return ModuleOutcome {
                    errors: vec![ElabError::Elab {
                        msg: NoPreviousImage {
                            module: module.name.clone(),
                            refusal: images.refusal(&module.name, &dependencies),
                        }
                        .to_string(),
                        span: heather_syntax::Span { start: 0, end: 0 },
                    }],
                    warnings: Vec::new(),
                    replayed: false,
                    replayed_items: 0,
                    forced_items: 0,
                    notices,
                };
            }
        };
        match elab.check_module_delta_only(&module.name, &module.src, dependencies, &previous.delta, force) {
            Ok((delta, report, met)) => {
                elab.take_omega_reports();
                self.replayed_items += report.replayed;
                self.only_met.extend(met.into_iter().map(|n| format!("{}::{n}", module.name)));
                // The interface a full check would have published, so later
                // modules replay over the same world; the image itself is
                // not written.
                self.interfaces.push(ModuleImageCache::interface_hash(&delta));
                ModuleOutcome {
                    errors: Vec::new(),
                    warnings: elab.take_warnings(),
                    replayed: false,
                    replayed_items: report.replayed,
                    forced_items: report.forced,
                    notices,
                }
            }
            Err(errors) => {
                self.images_usable = false;
                ModuleOutcome {
                    errors,
                    warnings: elab.take_warnings(),
                    replayed: false,
                    replayed_items: 0,
                    forced_items: 0,
                    notices,
                }
            }
        }
    }
}

impl WorldModule {
    fn new(name: String, range: Range<usize>, registry: Option<RegistryPart>) -> Self {
        Self { name, range, registry, digest: OnceLock::new(), index: OnceLock::new() }
    }

    fn registry_digest(&self, merkle: &[Option<Hash>]) -> Option<Hash> {
        *self.digest.get_or_init(|| {
            let projection = self.registry.as_ref()?.projection(&mut MerkleHasher(merkle))?;
            Some(heather_cache::sha256::sha256(&projection))
        })
    }

    fn index(&self, merkle: &[Option<Hash>]) -> &HashMap<Hash, Vec<usize>> {
        self.index.get_or_init(|| {
            let mut index: HashMap<Hash, Vec<usize>> = HashMap::new();
            for at in self.range.clone() {
                if let Some(Some(hash)) = merkle.get(at) {
                    index.entry(*hash).or_default().push(at);
                }
            }
            index
        })
    }
}

fn put_str(h: &mut Sha256, s: &str) {
    h.update(&(s.len() as u64).to_le_bytes());
    h.update(s.as_bytes());
}
