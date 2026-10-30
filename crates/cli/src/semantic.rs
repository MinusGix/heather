//! Cache-aware semantic module loading without presentation policy.
//!
//! A module is elaborated over its import closure and nothing else, in the
//! closure's canonical order (`docs/module-dag-design.md`): the session keeps,
//! per module it has finished, that module's identity and canonical world,
//! builds the next module's world from the worlds of its imports, and keys
//! its image by its source and its closure's identities alone. So a module
//! means one thing in every process, whatever else the process loads, and
//! modules that do not import one another can be built apart. An image is
//! loaded into any other world by moving it there; every replay is bounded,
//! kernel-checked or vouched for by the verdict store, and this component
//! never installs the separate trusted declaration cache gate. Diagnostics,
//! warnings and cache notices go back to the caller.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::io::Write as _;
use std::ops::Range;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::OnceLock;

use heather_cache::merkle::{self, Hash};
use heather_cache::module_image::{
    ImageFreshness, ImageRefusal, ModuleCacheKey, ModuleImageCache, SemanticsIdentity, SourceKey,
    WorldRecord, WorldReference,
};
use heather_cache::sha256::Sha256;
use heather_elab::{
    ElabError, Elaborator, LintProfile, ModuleDelta, ModuleDependencyIdentity, NameWorld,
    RegistryPart, RelocationTarget, SemanticImage, Warning, WorldHasher, source_identifiers, stats,
};
use heather_kernel::term::{GlobalBinding, GlobalCtx, Term, Type};

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

/// One module of the world under a module, in that world's order: what
/// relocating a later module needs to know about it
/// (`docs/module-interface-cutoff-design.md`).
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

/// The canonical order of a module's closure without the module
/// (`docs/module-dag-design.md` §2): `order[..spine]` is the canonical
/// order of its largest import with that import last, so the world under the
/// module extends that import's world by `order[spine..]`.
#[derive(Clone, Default)]
struct Canon {
    order: Rc<Vec<String>>,
    spine: usize,
}

/// What the session keeps of a module it has finished, in the module's own
/// canonical coordinates.
struct Finished {
    /// The imports the session had finished when it checked the module, in
    /// name order: the edges its canonical order is taken over.
    imports: Vec<String>,
    canon: Canon,
    /// Its imports, or theirs, did not check, or it did not: no world holds
    /// it, and nothing that imports it is checked.
    failed: bool,
    /// The bindings it adds.
    len: usize,
    /// Its interface hash over its canonical world: what keys its
    /// dependents (§5).
    identity: [u8; 32],
    key: ModuleCacheKey,
    source_len: usize,
    registry: Option<RegistryPart>,
    /// The digest of [`Self::registry`]'s projection, position-independent,
    /// once taken.
    digest: OnceLock<Option<Hash>>,
    /// Content hash per binding, once taken; position-independent.
    hashes: Option<Rc<Vec<Option<Hash>>>>,
    /// Its delta over its canonical world, when held; otherwise the store
    /// has it under [`Self::key`].
    delta: Option<Rc<ModuleDelta>>,
    /// The canonical world after it, once built.
    state: Option<SemanticImage>,
}

/// The prelude's world: what every canonical world starts from.
struct Base {
    image: SemanticImage,
    len: usize,
    hashes: Option<Rc<Vec<Option<Hash>>>>,
}

/// State for one checked closure.
pub struct SemanticSession {
    images: Option<ModuleImageCache>,
    images_usable: bool,
    freshness: ImageFreshness,
    hits: usize,
    stale_hits: usize,
    relocated: usize,
    replayed_items: usize,
    /// Whether the caller's elaborator accumulates every module checked, in
    /// the caller's order (the default: a consumer reads the world it
    /// loaded). Without it the caller's elaborator only configures the
    /// worlds modules are checked in, which saves moving each module into
    /// one more world.
    process_world: bool,
    /// The modules in the caller's elaborator, in order, with their Ψ ranges.
    process: Vec<(String, Range<usize>)>,
    base: Option<Base>,
    done: HashMap<String, Finished>,
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
            freshness: ImageFreshness::Exact,
            hits: 0,
            stale_hits: 0,
            relocated: 0,
            replayed_items: 0,
            process_world: true,
            process: Vec::new(),
            base: None,
            done: HashMap::new(),
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

    /// Leave the caller's elaborator out of the checked world: each module
    /// is checked in its own canonical world and only there, and the
    /// elaborator passed to [`Self::check`] is the configuration those
    /// worlds are made with (its gate, width, lints, collectors). For a
    /// driver that reads nothing back from it, like `heather check`.
    pub fn without_process_world(mut self) -> Self {
        self.process_world = false;
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

    /// Check or replay the next module, over its import closure alone
    /// (`docs/module-dag-design.md` §2). Every module it imports must have
    /// been given to the session before it; an import the session has not
    /// seen is left to the elaborator to report. A module whose closure holds
    /// a module that did not check is not checked: there is no world to
    /// check it in.
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
        // The profile is part of the image key, so the lints the module is
        // elaborated under are the ones it is keyed by.
        elab.set_lint_profile(lint_profile);
        if self.base.is_none() {
            self.base = Some(Base { image: elab.semantic_image(), len: elab.psi().bindings.len(), hashes: None });
        }
        let mut imports: Vec<String> =
            written_imports(&module.src).into_iter().filter(|m| self.done.contains_key(m)).collect();
        imports.sort();
        imports.dedup();
        let canon = self.canon_of(&imports);
        let source_len = module.src.len();
        let failed_import = canon.order.iter().find(|m| self.done[*m].failed).cloned();
        if let Some(failed) = failed_import {
            self.done.insert(module.name.clone(), Finished::failed(imports, canon, source_len));
            return ModuleOutcome {
                errors: vec![ElabError::Elab {
                    msg: format!(
                        "module `{}` is not checked: its import closure holds `{failed}`, which did not check",
                        module.name
                    ),
                    span: heather_syntax::Span { start: 0, end: 0 },
                }],
                warnings: Vec::new(),
                replayed: false,
                replayed_items: 0,
                forced_items: 0,
                notices: Vec::new(),
            };
        }
        let dependencies =
            ModuleDependencyIdentity::new(canon.order.iter().map(|m| self.done[m].identity).collect());
        let key = ModuleCacheKey::for_source(&module.name, &module.src, &dependencies, lint_profile);
        let source = SourceKey::for_source(&module.name, &module.src, lint_profile);
        let in_place = self.process_world
            && self.process.len() == canon.order.len()
            && self.process.iter().zip(canon.order.iter()).all(|((n, _), m)| n == m);

        // A hit moved straight into the caller's world: the canonical world
        // under the module is needed only to elaborate it.
        if self.process_world && !in_place && self.images_usable && !self.only.contains_key(&module.name) {
            if let Some(outcome) = self.hit_into_process(elab, module, key, &dependencies, &imports, &canon) {
                return outcome;
            }
        }

        let start = elab.psi().bindings.len();
        let (outcome, delta, state) = if in_place {
            let (outcome, delta) = self.check_in(elab, module, lint_profile, key, source, dependencies, &canon);
            let state = delta.as_ref().map(|_| elab.semantic_image());
            (outcome, delta, state)
        } else {
            let mut world = match stats::timed(stats::Timer::ImageRecheck, || self.world_before(elab, &canon)) {
                Ok(world) => world,
                Err(why) => {
                    self.done.insert(module.name.clone(), Finished::failed(imports, canon, source_len));
                    return internal_failure(&module.name, why);
                }
            };
            let (outcome, delta) = self.check_in(&mut world, module, lint_profile, key, source, dependencies, &canon);
            let state = delta.as_ref().map(|_| world.semantic_image());
            (outcome, delta, state)
        };
        let Some(delta) = delta else {
            self.done.insert(module.name.clone(), Finished::failed(imports, canon, source_len));
            return outcome;
        };
        let finished = Finished {
            imports,
            canon,
            failed: false,
            len: delta.binding_count(),
            identity: ModuleImageCache::interface_hash(&delta),
            key,
            source_len,
            registry: Some(delta.registry_part()),
            digest: OnceLock::new(),
            hashes: None,
            delta: Some(Rc::new(delta)),
            state,
        };
        self.done.insert(module.name.clone(), finished);
        if self.process_world {
            if !in_place {
                let delta = self.done[&module.name].delta.clone().expect("held");
                if let Err(why) = self.into_process(elab, &module.name, &delta) {
                    self.done.get_mut(&module.name).expect("finished").failed = true;
                    return internal_failure(&module.name, why);
                }
            }
            let end = elab.psi().bindings.len();
            self.process.push((module.name.clone(), start..end));
        }
        outcome
    }

    /// Whether `module` was refused only because a module of its import
    /// closure did not check: its one error restates that module's, which a
    /// caller reporting every module has already shown.
    pub fn blocked_by_import(&self, module: &str) -> bool {
        self.done.get(module).is_some_and(|m| m.failed && m.canon.order.iter().any(|d| self.done[d].failed))
    }

    /// Whether checking `module` now would wait for another process that is
    /// building its image (`ModuleImageCache::being_built`). Its imports must
    /// have been checked.
    pub fn built_elsewhere(&self, module: &Module, imports: &[String], lint_profile: LintProfile) -> bool {
        let Some(images) = self.images.as_ref().filter(|_| self.images_usable) else { return false };
        let mut imports: Vec<String> = imports.iter().filter(|m| self.done.contains_key(*m)).cloned().collect();
        imports.sort();
        imports.dedup();
        let canon = self.canon_of(&imports);
        if canon.order.iter().any(|m| self.done[m].failed) {
            return false;
        }
        let dependencies =
            ModuleDependencyIdentity::new(canon.order.iter().map(|m| self.done[m].identity).collect());
        images.being_built(ModuleCacheKey::for_source(&module.name, &module.src, &dependencies, lint_profile))
    }

    /// The canonical order of the closure of a module with these imports
    /// (`docs/module-dag-design.md` §2), from the finished modules' own.
    fn canon_of(&self, imports: &[String]) -> Canon {
        let Some(big) = imports
            .iter()
            .max_by(|a, b| self.done[*a].canon.order.len().cmp(&self.done[*b].canon.order.len()).then(b.cmp(a)))
        else {
            return Canon::default();
        };
        let mut order: Vec<String> = (*self.done[big].canon.order).clone();
        order.push(big.clone());
        let spine = order.len();
        let mut placed: HashSet<String> = order.iter().cloned().collect();
        fn visit(done: &HashMap<String, Finished>, m: &str, placed: &mut HashSet<String>, order: &mut Vec<String>) {
            if placed.contains(m) {
                return;
            }
            for d in &done[m].imports {
                visit(done, d, placed, order);
            }
            placed.insert(m.to_string());
            order.push(m.to_string());
        }
        for m in imports {
            visit(&self.done, m, &mut placed, &mut order);
        }
        Canon { order: Rc::new(order), spine }
    }

    /// Ψ length of the world `order` (after the prelude).
    fn world_len(&self, order: &[String]) -> usize {
        self.base.as_ref().expect("base").len + order.iter().map(|m| self.done[m].len).sum::<usize>()
    }

    /// An elaborator configured as `template` over the canonical world
    /// `canon`: the world of its largest import, extended by the rest
    /// (`docs/module-dag-design.md` §6).
    fn world_before(&mut self, template: &Elaborator, canon: &Canon) -> Result<Elaborator, String> {
        let image = match canon.spine {
            0 => self.base.as_ref().expect("base").image.clone(),
            k => self.state_of(template, &canon.order[k - 1].clone())?,
        };
        let mut world = template.fork_over(&image);
        for i in canon.spine..canon.order.len() {
            let order = Rc::clone(&canon.order);
            self.load_into(&mut world, &order[i], &order[..i])?;
        }
        Ok(world)
    }

    /// The canonical world after `name`, built once.
    fn state_of(&mut self, template: &Elaborator, name: &str) -> Result<SemanticImage, String> {
        if let Some(state) = &self.done[name].state {
            return Ok(state.clone());
        }
        let canon = self.done[name].canon.clone();
        let mut world = self.world_before(template, &canon)?;
        self.load_into(&mut world, name, &canon.order)?;
        let state = world.semantic_image();
        self.done.get_mut(name).expect("finished").state = Some(state.clone());
        Ok(state)
    }

    /// `name`'s delta over its canonical world: held, or decoded from the
    /// store against a placeholder prefix of that world's length.
    fn canonical_delta(&self, name: &str) -> Result<Rc<ModuleDelta>, String> {
        let f = &self.done[name];
        if let Some(delta) = &f.delta {
            return Ok(Rc::clone(delta));
        }
        let images = self.images.as_ref().ok_or("no image store holds it")?;
        let psi = placeholder(self.world_len(&f.canon.order));
        match stats::timed(stats::Timer::ImageDecode, || images.load(f.key, psi, f.source_len, self.freshness)) {
            Ok(Some(loaded)) => Ok(Rc::new(loaded.delta)),
            Ok(None) => Err(format!("the image of `{name}` is gone from the store")),
            Err(e) => Err(format!("the image of `{name}` is unusable: {e}")),
        }
    }

    /// Move `name`'s canonical delta into `world`, whose modules are
    /// `before`, and replay it there (`docs/module-dag-design.md` §4).
    fn load_into(&mut self, world: &mut Elaborator, name: &str, before: &[String]) -> Result<(), String> {
        let delta = self.canonical_delta(name)?;
        let f = &self.done[name];
        let moved = if f.canon.order[..] == *before {
            delta.over_prefix(world.psi().clone()).ok_or_else(|| format!("`{name}`'s world has another length"))?
        } else {
            let map = self.move_map(&f.canon.order, before.iter().map(String::as_str));
            delta
                .relocate(RelocationTarget {
                    dependency_psi: world.psi().clone(),
                    dependencies: delta.dependencies().clone(),
                    map: &mut |a| map.at(a),
                })
                .map_err(|e| format!("moving `{name}`: {e}"))?
        };
        stats::timed(stats::Timer::ImageRecheck, || world.replay_module_delta(&moved, delta.dependencies()))
            .map_err(|e| format!("replaying `{name}`: {e}"))
    }

    /// Move a canonical delta into the caller's world.
    fn into_process(&mut self, elab: &mut Elaborator, name: &str, delta: &ModuleDelta) -> Result<(), String> {
        let order = self.done[name].canon.order.clone();
        let map = self.move_map(&order, self.process.iter().map(|(n, _)| n.as_str()));
        let moved = delta
            .relocate(RelocationTarget {
                dependency_psi: elab.psi().clone(),
                dependencies: delta.dependencies().clone(),
                map: &mut |a| map.at(a),
            })
            .map_err(|e| format!("moving `{name}`: {e}"))?;
        stats::timed(stats::Timer::ImageRecheck, || elab.replay_module_delta(&moved, delta.dependencies()))
            .map_err(|e| format!("replaying `{name}`: {e}"))
    }

    /// The position map from the world `from` to a world whose modules are
    /// `to`, module by module: each module's bindings keep their layout.
    fn move_map<'a>(&self, from: &[String], to: impl Iterator<Item = &'a str>) -> MoveMap {
        let base = self.base.as_ref().expect("base").len;
        let mut at = base;
        let mut new_start = HashMap::new();
        for m in to {
            new_start.insert(m, at);
            at += self.done.get(m).map_or(0, |f| f.len);
        }
        let mut ranges = Vec::with_capacity(from.len());
        let mut at = base;
        for m in from {
            let len = self.done[m].len;
            ranges.push((at, at + len, new_start.get(m.as_str()).copied()));
            at += len;
        }
        MoveMap { base, ranges }
    }

    /// The world under a module checked in the caller's elaborator out of
    /// place, when the store has its image: moved there directly, never
    /// through the canonical world, which only elaboration needs. `None`
    /// sends the module down the canonical path, which reports what this
    /// one saw.
    fn hit_into_process(
        &mut self,
        elab: &mut Elaborator,
        module: &Module,
        key: ModuleCacheKey,
        dependencies: &ModuleDependencyIdentity,
        imports: &[String],
        canon: &Canon,
    ) -> Option<ModuleOutcome> {
        let images = self.images.as_ref()?;
        let psi = placeholder(self.world_len(&canon.order));
        let loaded = stats::timed(stats::Timer::ImageDecode, || images.load(key, psi, module.src.len(), self.freshness))
            .ok()??;
        if loaded.delta.dependencies() != dependencies {
            return None;
        }
        let start = elab.psi().bindings.len();
        let map = self.move_map(&canon.order, self.process.iter().map(|(n, _)| n.as_str()));
        let moved = loaded
            .delta
            .relocate(RelocationTarget {
                dependency_psi: elab.psi().clone(),
                dependencies: dependencies.clone(),
                map: &mut |a| map.at(a),
            })
            .ok()?;
        stats::timed(stats::Timer::ImageRecheck, || elab.replay_module_delta(&moved, dependencies)).ok()?;
        self.hits += 1;
        let mut notices = Vec::new();
        self.note_stale(&module.name, loaded.stale, &mut notices);
        // The canonical delta is not kept: the caller's world holds the moved
        // copy, and a later elaboration that needs this module's canonical
        // world decodes it again.
        self.done.insert(
            module.name.clone(),
            Finished {
                imports: imports.to_vec(),
                canon: canon.clone(),
                failed: false,
                len: loaded.delta.binding_count(),
                identity: loaded.interface_hash,
                key,
                source_len: module.src.len(),
                registry: Some(loaded.delta.registry_part()),
                digest: OnceLock::new(),
                hashes: None,
                delta: None,
                state: None,
            },
        );
        let end = elab.psi().bindings.len();
        self.process.push((module.name.clone(), start..end));
        Some(ModuleOutcome {
            errors: Vec::new(),
            warnings: loaded.warnings,
            replayed: true,
            replayed_items: 0,
            forced_items: 0,
            notices,
        })
    }

    fn note_stale(&mut self, module: &str, stale: Option<SemanticsIdentity>, notices: &mut Vec<CacheNotice>) {
        match stale {
            Some(writer) if writer == SemanticsIdentity::relocated() => {
                self.relocated += 1;
                notices.push(CacheNotice {
                    module: module.to_string(),
                    kind: CacheNoticeKind::Relocated,
                    error: "stored after an earlier relocation".into(),
                });
            }
            Some(writer) => {
                self.stale_hits += 1;
                notices.push(CacheNotice {
                    module: module.to_string(),
                    kind: CacheNoticeKind::StaleReplayed,
                    error: format!("build {} rather than {}", writer.short(), SemanticsIdentity::current().short()),
                });
            }
            None => {}
        }
    }

    /// Check or replay `module` in `elab`, whose world is exactly the
    /// canonical world `canon` under it. Returns the module's delta over
    /// that world when it checked.
    #[allow(clippy::too_many_arguments)]
    fn check_in(
        &mut self,
        elab: &mut Elaborator,
        module: &Module,
        lint_profile: LintProfile,
        key: ModuleCacheKey,
        source: SourceKey,
        dependencies: ModuleDependencyIdentity,
        canon: &Canon,
    ) -> (ModuleOutcome, Option<ModuleDelta>) {
        elab.set_lint_profile(lint_profile);
        let start = elab.psi().bindings.len();
        let mut notices = Vec::new();
        if !self.images_usable {
            let checked = elab.check_module_delta(&module.name, &module.src, dependencies);
            elab.take_omega_reports();
            return match checked {
                Ok(delta) => (
                    ModuleOutcome { errors: Vec::new(), warnings: elab.take_warnings(), replayed: false, replayed_items: 0, forced_items: 0, notices },
                    Some(delta),
                ),
                Err(errors) => (
                    ModuleOutcome { errors, warnings: elab.take_warnings(), replayed: false, replayed_items: 0, forced_items: 0, notices },
                    None,
                ),
            };
        }
        if let Some(force) = self.only.get(&module.name).cloned() {
            return self.check_only(elab, module, dependencies, force, notices);
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
                        self.hits += 1;
                        self.note_stale(&module.name, loaded.stale, &mut notices);
                        return (
                            ModuleOutcome {
                                errors: Vec::new(),
                                warnings: loaded.warnings,
                                replayed: true,
                                replayed_items: 0,
                                forced_items: 0,
                                notices,
                            },
                            Some(loaded.delta),
                        );
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
        let (world, merkle) = stats::timed(stats::Timer::ImageRelocate, || self.world_view(elab, canon));
        let view = stats::timed(stats::Timer::ImageRelocate, || observe_world(&world, &merkle, elab, module));
        if view.is_none() && std::env::var_os("HEATHER_RELOCATION_DEBUG").is_some() {
            eprintln!("relocation-debug {}: no world view", module.name);
        }
        let mut audited = None;
        if let Some(view) = &view {
            match self.freshness {
                ImageFreshness::AcceptStale => {
                    match stats::timed(stats::Timer::ImageRelocate, || {
                        self.relocation(&world, &merkle, elab, module, source, &dependencies, view)
                    }) {
                        Relocation::Moved { delta, warnings, lookups } => match stats::timed(stats::Timer::ImageRecheck, || {
                            elab.replay_module_delta(&delta, &dependencies)
                        }) {
                            Ok(()) => {
                                self.hits += 1;
                                self.relocated += 1;
                                notices.push(CacheNotice {
                                    module: module.name.clone(),
                                    kind: CacheNoticeKind::Relocated,
                                    error: "registries and the names it wrote unchanged".into(),
                                });
                                let record = world_record(&world, &merkle, start, &delta, view, lookups);
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
                                return (
                                    ModuleOutcome {
                                        errors: Vec::new(),
                                        warnings,
                                        replayed: true,
                                        replayed_items: 0,
                                        forced_items: 0,
                                        notices,
                                    },
                                    Some(delta),
                                );
                            }
                            Err(error) => notices.push(CacheNotice {
                                module: module.name.clone(),
                                kind: CacheNoticeKind::RelocationRejected,
                                error: error.to_string(),
                            }),
                        },
                        Relocation::NoCandidate => {
                            if std::env::var_os("HEATHER_RELOCATION_DEBUG").is_some() {
                                eprintln!("relocation-debug {}: no candidate", module.name);
                            }
                        }
                        Relocation::Refused(why) => {
                            if std::env::var_os("HEATHER_RELOCATION_DEBUG").is_some() {
                                eprintln!("relocation-debug {}: refused: {why}", module.name);
                            }
                        }
                    }
                }
                ImageFreshness::Exact if self.audit.is_some() => {
                    audited = Some(self.relocation(&world, &merkle, elab, module, source, &dependencies, view));
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
                return (
                    ModuleOutcome {
                        errors,
                        warnings: elab.take_warnings(),
                        replayed: false,
                        replayed_items: 0,
                        forced_items: 0,
                        notices,
                    },
                    None,
                );
            }
        };
        self.replayed_items += replayed_items;
        let warnings = elab.take_warnings();
        if let Some(audited) = audited {
            self.audit(&module.name, audited, &delta);
        }
        let record = view.zip(lookups).and_then(|(view, lookups)| {
            stats::timed(stats::Timer::ImageRelocate, || world_record(&world, &merkle, start, &delta, &view, lookups))
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
        (ModuleOutcome { errors: Vec::new(), warnings, replayed: false, replayed_items, forced_items: 0, notices }, Some(delta))
    }

    /// The world under a module whose world is `canon`, as the early cutoff
    /// reads it: its modules with their registry contributions, and a
    /// content hash per binding. Hashes and digests are position-independent,
    /// so each module's are taken once and reused in every world.
    fn world_view(&mut self, elab: &Elaborator, canon: &Canon) -> (Vec<WorldModule>, Vec<Option<Hash>>) {
        let psi = elab.psi();
        let base = self.base.as_mut().expect("base");
        let base_len = base.len;
        let base_hashes = match &base.hashes {
            Some(h) => Rc::clone(h),
            None => {
                let mut merkle = Vec::with_capacity(base_len);
                hash_bindings(elab, psi, 0..base_len, &mut merkle);
                let h = Rc::new(merkle);
                base.hashes = Some(Rc::clone(&h));
                h
            }
        };
        let mut merkle: Vec<Option<Hash>> = Vec::with_capacity(psi.bindings.len());
        merkle.extend(base_hashes.iter().copied());
        let mut world = Vec::with_capacity(canon.order.len() + 1);
        if base_len > 0 {
            world.push(WorldModule::new(BASE_MODULE.into(), 0..base_len, None));
        }
        for m in canon.order.iter() {
            let at = merkle.len();
            let f = self.done.get_mut(m).expect("finished");
            match &f.hashes {
                Some(h) => merkle.extend(h.iter().copied()),
                None => {
                    hash_bindings(elab, psi, at..at + f.len, &mut merkle);
                    f.hashes = Some(Rc::new(merkle[at..].to_vec()));
                }
            }
            let wm = WorldModule::new(m.clone(), at..at + f.len, f.registry.clone().or_else(|| Some(RegistryPart::unknown())));
            if let Some(d) = f.digest.get() {
                let _ = wm.digest.set(*d);
            }
            world.push(wm);
        }
        // Digests taken here are kept for the next world.
        for wm in &world {
            if let Some(f) = self.done.get(&wm.name)
                && f.digest.get().is_none()
                && wm.registry.as_ref().is_some_and(|p| !p.is_inert())
            {
                let _ = f.digest.set(wm.registry_digest(&merkle));
            }
        }
        (world, merkle)
    }

    /// Look for an image of this exact source over another world, and move
    /// it onto this one if nothing it observed differs: the world's
    /// registries and what its identifiers resolve to are unchanged, and
    /// every binding it refers to is found again, by content, in the module
    /// it came from (`docs/module-interface-cutoff-design.md` §3). The moved
    /// delta is not replayed here.
    #[allow(clippy::too_many_arguments)]
    fn relocation(
        &self,
        world: &[WorldModule],
        merkle: &[Option<Hash>],
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
        if Some(record.names) != names_digest(world, merkle, view, &record.lookups) {
            return Relocation::Refused("a name the module wrote resolves differently".into());
        }
        let by_name: HashMap<&str, &WorldModule> = world.iter().map(|m| (m.name.as_str(), m)).collect();
        let mut map = HashMap::with_capacity(record.references.len());
        for r in &record.references {
            let Some(m) = by_name.get(record.modules[r.module as usize].as_str()) else {
                return Relocation::Refused(format!("module `{}` is not in this world", record.modules[r.module as usize]));
            };
            match m.index(merkle).get(&r.hash) {
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
    ) -> (ModuleOutcome, Option<ModuleDelta>) {
        let images = self.images.as_ref().expect("usable images have a cache");
        let previous = stats::timed(stats::Timer::ImageDecode, || {
            images.load_previous(&module.name, &dependencies, elab.psi().clone(), self.freshness)
        });
        let refused = |notices: Vec<CacheNotice>| {
            (
                ModuleOutcome {
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
                },
                None,
            )
        };
        let previous = match previous {
            Ok(Some(previous)) => previous,
            Ok(None) => return refused(notices),
            Err(error) => {
                notices.push(CacheNotice {
                    module: module.name.clone(),
                    kind: CacheNoticeKind::PreviousUnusable,
                    error: error.to_string(),
                });
                return refused(notices);
            }
        };
        match elab.check_module_delta_only(&module.name, &module.src, dependencies, &previous.delta, force) {
            Ok((delta, report, met)) => {
                elab.take_omega_reports();
                self.replayed_items += report.replayed;
                self.only_met.extend(met.into_iter().map(|n| format!("{}::{n}", module.name)));
                // The delta a full check would have published, so later
                // modules are checked over the same world; the image itself
                // is not written.
                (
                    ModuleOutcome {
                        errors: Vec::new(),
                        warnings: elab.take_warnings(),
                        replayed: false,
                        replayed_items: report.replayed,
                        forced_items: report.forced,
                        notices,
                    },
                    Some(delta),
                )
            }
            Err(errors) => (
                ModuleOutcome {
                    errors,
                    warnings: elab.take_warnings(),
                    replayed: false,
                    replayed_items: 0,
                    forced_items: 0,
                    notices,
                },
                None,
            ),
        }
    }
}

impl Finished {
    fn failed(imports: Vec<String>, canon: Canon, source_len: usize) -> Self {
        Finished {
            imports,
            canon,
            failed: true,
            len: 0,
            identity: [0; 32],
            key: ModuleCacheKey::for_source("", "", &ModuleDependencyIdentity::default(), LintProfile::Default),
            source_len,
            registry: None,
            digest: OnceLock::new(),
            hashes: None,
            delta: None,
            state: None,
        }
    }
}

/// [`SemanticSession::move_map`]'s map: old position to new.
struct MoveMap {
    base: usize,
    /// Per module of the old world, in order: its old range and its new
    /// start, `None` when the new world does not hold it.
    ranges: Vec<(usize, usize, Option<usize>)>,
}

impl MoveMap {
    fn at(&self, a: usize) -> Option<usize> {
        if a < self.base {
            return Some(a);
        }
        let i = self.ranges.partition_point(|&(_, end, _)| end <= a);
        let &(start, end, new) = self.ranges.get(i)?;
        (start..end).contains(&a).then_some(new? + (a - start))
    }
}

/// A prefix of `len` bindings that are nobody: what an image is decoded
/// against when it is moved before it is replayed. Its length is all the
/// decoder reads of it, and the move replaces it before the replay compares
/// the prefix with the world's.
fn placeholder(len: usize) -> GlobalCtx {
    GlobalCtx::new(vec![GlobalBinding::Ctx; len])
}

/// The modules a source imports, as written, the prelude aside. The loader
/// read the same lines; a parse error is the elaborator's to report.
pub fn written_imports(src: &str) -> Vec<String> {
    match heather_syntax::parse_file(src) {
        Ok(file) => file
            .items
            .iter()
            .filter_map(|item| match item {
                heather_syntax::Item::Import(imp) if imp.module != heather_elab::PRELUDE_MODULE => Some(imp.module.clone()),
                _ => None,
            })
            .collect(),
        Err(_) => Vec::new(),
    }
}

fn internal_failure(module: &str, why: String) -> ModuleOutcome {
    ModuleOutcome {
        errors: vec![ElabError::Elab {
            msg: format!("module `{module}` could not be placed in its world: {why}"),
            span: heather_syntax::Span { start: 0, end: 0 },
        }],
        warnings: Vec::new(),
        replayed: false,
        replayed_items: 0,
        forced_items: 0,
        notices: Vec::new(),
    }
}

/// Content hashes for `range` of `psi`, appended to `merkle`, which holds
/// the hashes of everything before it.
/// An assumption hashes in its own domain, as in the verdict store: a
/// theorem turned into an assumption of the same statement is a change.
fn hash_bindings(elab: &Elaborator, psi: &GlobalCtx, range: Range<usize>, merkle: &mut Vec<Option<Hash>>) {
    for at in range {
        let binding = psi.bindings.get(at).expect("in the world");
        let h = if elab.is_assumption_at(at) {
            merkle::assumption_interface_hash(merkle, binding)
        } else {
            merkle::interface_hash(merkle, binding)
        };
        merkle.push(h);
    }
}

/// The registry digest and name digest of the world under `module`
/// (`docs/module-interface-cutoff-design.md` §2); `None` when some part
/// of it cannot be hashed, which only ever costs a relocation.
fn observe_world(world: &[WorldModule], merkle: &[Option<Hash>], elab: &Elaborator, module: &Module) -> Option<WorldView> {
    let mut registry = Sha256::new();
    registry.update(b"heather/world-registry/1\0");
    for m in world {
        match &m.registry {
            None => {
                put_str(&mut registry, &m.name);
                for at in m.range.clone() {
                    registry.update(&merkle[at]?);
                }
            }
            Some(part) if part.is_inert() => {}
            Some(_) => {
                put_str(&mut registry, &m.name);
                registry.update(&m.registry_digest(merkle)?);
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
fn names_digest(world: &[WorldModule], merkle: &[Option<Hash>], view: &WorldView, lookups: &[String]) -> Option<Hash> {
    let lookups: BTreeSet<&str> = lookups.iter().map(String::as_str).collect();
    let wanted = |name: &str| view.identifiers.contains(name) || lookups.contains(name);
    let observed = view.names.observations(&wanted);
    let mut names = Sha256::new();
    names.update(b"heather/world-names/2\0");
    names.update(&(observed.bytes.len() as u64).to_le_bytes());
    names.update(&observed.bytes);
    for at in observed.globals {
        names.update(&(*merkle.get(at)?)?);
    }
    // A module name it wrote or looked up is a qualifier it may have
    // resolved.
    for m in world {
        if wanted(&m.name) {
            put_str(&mut names, &m.name);
        }
    }
    Some(names.finish())
}

/// The world record a published image of `delta` carries: its
/// dependency references by content, and the digests of `view`.
fn world_record(
    world: &[WorldModule],
    merkle: &[Option<Hash>],
    base: usize,
    delta: &ModuleDelta,
    view: &WorldView,
    lookups: Vec<String>,
) -> Option<WorldRecord> {
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
        let module = world.partition_point(|m| m.range.end <= at);
        let m = world.get(module).filter(|m| m.range.contains(&at))?;
        let hash = (*merkle.get(at)?)?;
        let same = m.index(merkle).get(&hash)?;
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
        modules: world.iter().map(|m| m.name.clone()).collect(),
        references,
        registry: view.registry,
        names: names_digest(world, merkle, view, &lookups)?,
        lookups,
    })
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
