//! Cache-aware semantic module loading without presentation policy.
//!
//! A session follows one topologically ordered import closure. It owns the
//! exact-prefix identity required by the current absolute-Ψ image format and
//! returns diagnostics, warnings and cache notices to its caller. Cache hits
//! are always bounded, kernel-checked semantic replay; this component never
//! installs the separate trusted declaration cache gate.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::PathBuf;

use heather_cache::module_image::{ImageFreshness, ModuleCacheKey, ModuleImageCache, SemanticsIdentity};
use heather_elab::{ElabError, Elaborator, LintProfile, ModuleDependencyIdentity, Warning, stats};

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

/// State for one accepted, topologically ordered module closure.
pub struct SemanticSession {
    images: Option<ModuleImageCache>,
    interfaces: Vec<[u8; 32]>,
    images_usable: bool,
    freshness: ImageFreshness,
    hits: usize,
    stale_hits: usize,
    replayed_items: usize,
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
#[derive(Debug)]
pub struct NoPreviousImage {
    pub module: String,
}

impl fmt::Display for NoPreviousImage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "--only: no stored image of module `{}` over these dependencies to replay the \
             prefix from. Either it has not been checked with `--cache` over these \
             dependencies yet — run `heather check --cache` on the file once first — or its \
             image was refused as too large to store, which that run reports as `cache: could \
             not store module `{}``; a module whose image does not fit cannot be probed with \
             --only at all",
            self.module, self.module
        )
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
            replayed_items: 0,
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

        let dependencies = ModuleDependencyIdentity::new(self.interfaces.clone());
        let key = ModuleCacheKey::for_source(
            &module.name,
            &module.src,
            &dependencies,
            lint_profile,
        );
        let images = self.images.as_ref().expect("usable images have a cache");
        let mut notices = Vec::new();
        if let Some(force) = self.only.get(&module.name).cloned() {
            return self.check_only(elab, module, dependencies, force, notices);
        }
        // The three phases warm replay is made of — read/checksum/decode, the
        // kernel recheck of the decoded delta, and publication (render plus
        // hash). The fast lane's premise rests on these
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
                    if let Some(writer) = loaded.stale {
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
                    return ModuleOutcome {
                        errors: Vec::new(),
                        warnings: loaded.warnings,
                        replayed: true,
                        replayed_items: 0,
                        forced_items: 0,
                        notices,
                    };
                }
                Err(error) => notices.push(CacheNotice {
                    module: module.name.clone(),
                    kind: CacheNoticeKind::ReplayRejected,
                    error: error.to_string(),
                }),
            },
            Ok(None) => {}
            Err(error) => notices.push(CacheNotice {
                module: module.name.clone(),
                kind: CacheNoticeKind::LoadRejected,
                error: error.to_string(),
            }),
        }

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
        let checked = match &previous {
            Some(previous) => elab
                .check_module_delta_from(&module.name, &module.src, dependencies, &previous.delta)
                .map(|(delta, report)| (delta, report.replayed)),
            None => elab
                .check_module_delta(&module.name, &module.src, dependencies)
                .map(|delta| (delta, 0)),
        };
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
        if let Err(error) =
            stats::timed(stats::Timer::ImagePublish, || images.publish(key, &delta, &warnings))
        {
            notices.push(CacheNotice {
                module: module.name.clone(),
                kind: CacheNoticeKind::PublishFailed,
                error: error.to_string(),
            });
        }
        ModuleOutcome { errors: Vec::new(), warnings, replayed: false, replayed_items, forced_items: 0, notices }
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
                        msg: NoPreviousImage { module: module.name.clone() }.to_string(),
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
                        msg: NoPreviousImage { module: module.name.clone() }.to_string(),
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
