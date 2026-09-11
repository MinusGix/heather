//! Cache-aware semantic module loading without presentation policy.
//!
//! A session follows one topologically ordered import closure. It owns the
//! exact-prefix identity required by the current absolute-Ψ image format and
//! returns diagnostics, warnings and cache notices to its caller. Cache hits
//! are always bounded, kernel-checked semantic replay; this component never
//! installs the separate trusted declaration cache gate.

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
            CacheNoticeKind::StaleReplayed => write!(
                f,
                "cache: module `{}` replayed from an image of another build ({}), kernel-rechecked; a run without stale images re-elaborates it",
                self.module, self.error
            ),
        }
    }
}

pub struct ModuleOutcome {
    pub errors: Vec<ElabError>,
    pub warnings: Vec<Warning>,
    pub replayed: bool,
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
        }
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

        let delta = match elab.check_module_delta(&module.name, &module.src, dependencies) {
            Ok(delta) => {
                // Drained, not printed: where an `omega` invocation's time went
                // is the dump's `omega_*` columns now, attributed by
                // declaration rather than by invocation
                // (`docs/instrumentation-design.md` §4). The per-invocation
                // reports stay available through `take_omega_reports`.
                elab.take_omega_reports();
                delta
            }
            Err(errors) => {
                self.images_usable = false;
                return ModuleOutcome {
                    errors,
                    warnings: elab.take_warnings(),
                    replayed: false,
                    notices,
                };
            }
        };
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
        ModuleOutcome { errors: Vec::new(), warnings, replayed: false, notices }
    }
}
