//! Content-addressed persistent storage for checked semantic module images.
//!
//! This layer owns filesystem and rebuild policy; `heather-elab` owns only
//! the semantic bytes and their bounded inert decoder. A cache hit is still
//! replayed through the kernel before publication.

use std::fmt;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use heather_elab::{
    Lint, LintFix, LintProfile, ModuleDelta, ModuleDependencyIdentity, ModuleImageDecodeError,
    ModuleImageLimits, Span, Warning,
};
use heather_kernel::term::GlobalCtx;

use crate::sha256::{Sha256, hex, sha256};
use crate::{ELABORATOR_SEMANTICS, KERNEL_SEMANTICS};

const MAGIC: &[u8; 8] = b"HTHCACH\x06";
const DOMAIN_KEY: &[u8] = b"heather/module-cache-key/3\0";
const DOMAIN_INTERFACE: &[u8] = b"heather/module-interface/1\0";
const DOMAIN_SEMANTICS: &[u8] = b"heather/module-semantics/1\0";
const DOMAIN_RELOCATED: &[u8] = b"heather/module-relocated/1\0";
const DOMAIN_SOURCE: &[u8] = b"heather/module-source/1\0";
/// magic, cache key, producing semantics, interface hash, semantic length,
/// warning count, world-record length, expected refusals. The first 104 bytes are what
/// `scripts/sentinel` reads; they keep their places across format versions.
const HEADER: usize = 8 + 32 + 32 + 32 + 8 + 8 + 8 + 8;
const CHECKSUM: usize = 32;
static TEMP_ID: AtomicU64 = AtomicU64::new(0);

/// Which elaborator and kernel produced an image.
///
/// This is deliberately **not** part of [`ModuleCacheKey`]: the key names
/// *what* was elaborated (source, dependencies, options), the semantics
/// identity names *who* elaborated it. Keeping them apart lets a reader choose
/// [`ImageFreshness::AcceptStale`] and replay an image its own build did not
/// write — sound, because replay rechecks every kernel binding with the
/// reader's kernel — instead of paying a cold rebuild after every edit to the
/// compiler's Rust sources.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticsIdentity([u8; 32]);

impl SemanticsIdentity {
    /// The identity of this build: the elaborator fingerprint (which already
    /// covers the kernel's sources) and the kernel fingerprint, hashed
    /// together.
    pub fn current() -> Self {
        Self::of(ELABORATOR_SEMANTICS, KERNEL_SEMANTICS)
    }

    /// An identity for arbitrary fingerprints. Tests and tools use it to
    /// stand in for another build; ordinary code wants [`Self::current`].
    pub fn of(elaborator: &str, kernel: &str) -> Self {
        let mut h = Sha256::new();
        h.update(DOMAIN_SEMANTICS);
        put_bytes(&mut h, elaborator.as_bytes());
        put_bytes(&mut h, kernel.as_bytes());
        Self(h.finish())
    }

    pub fn bytes(self) -> [u8; 32] {
        self.0
    }

    /// The identity an image carries when it was not elaborated but
    /// **relocated** by this build from an image of the same source over
    /// another dependency world (`docs/module-interface-cutoff-design.md`).
    /// It is not [`Self::current`], so [`ImageFreshness::Exact`] never
    /// replays one: the exact lane keeps elaborating every module it
    /// misses, and stays the reference the relocation is compared against.
    pub fn relocated() -> Self {
        let mut h = Sha256::new();
        h.update(DOMAIN_RELOCATED);
        h.update(&Self::current().0);
        Self(h.finish())
    }

    /// A short rendering for notices.
    pub fn short(self) -> String {
        hex(&self.0).chars().take(12).collect()
    }
}

/// How a reader treats an image produced by a different build.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ImageFreshness {
    /// Only images this exact elaborator and kernel wrote are replayed; any
    /// other is an ordinary miss and is rebuilt (and overwritten). The final
    /// gate: a warm run proves the *current* frontend still produces this
    /// world.
    #[default]
    Exact,
    /// Images from any build whose format this reader decodes are replayed,
    /// kernel-rechecked as always, and reported as stale. Sound by
    /// construction; what it does not verify is that the current frontend
    /// would elaborate the unchanged module identically. An inner-loop
    /// policy, never a final verification's.
    AcceptStale,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ModuleCacheKey([u8; 32]);

impl ModuleCacheKey {
    /// The content identity of an elaboration: module name, exact source,
    /// checking options and the ordered dependency interfaces. The producing
    /// build is recorded in the artifact instead ([`SemanticsIdentity`]), so
    /// a source that has not changed keeps one key across compiler edits.
    pub fn for_source(
        module: &str,
        source: &str,
        dependencies: &ModuleDependencyIdentity,
        lint_profile: LintProfile,
    ) -> Self {
        let mut h = Sha256::new();
        h.update(DOMAIN_KEY);
        put_bytes(&mut h, module.as_bytes());
        h.update(&sha256(source.as_bytes()));
        h.update(&[match lint_profile {
            LintProfile::Default => 0,
            LintProfile::Stdlib => 1,
        }]);
        h.update(&(dependencies.ordered_interface_hashes().len() as u64).to_le_bytes());
        for dependency in dependencies.ordered_interface_hashes() {
            h.update(dependency);
        }
        Self(h.finish())
    }

    pub fn bytes(self) -> [u8; 32] {
        self.0
    }
}

/// The identity of a module's source alone — name, text, lint profile — with
/// no dependency world: what finds a relocation candidate, an image of the
/// same text over another world (`docs/module-interface-cutoff-design.md`
/// §2). Never a cache key: what the candidate is accepted on is its world
/// record, checked against the world it is moved onto.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceKey([u8; 32]);

impl SourceKey {
    pub fn for_source(module: &str, source: &str, lint_profile: LintProfile) -> Self {
        let mut h = Sha256::new();
        h.update(DOMAIN_SOURCE);
        put_bytes(&mut h, module.as_bytes());
        h.update(&sha256(source.as_bytes()));
        h.update(&[match lint_profile {
            LintProfile::Default => 0,
            LintProfile::Stdlib => 1,
        }]);
        Self(h.finish())
    }
}

/// What an image records about the dependency world it was elaborated over,
/// so it can be moved onto another world that differs only in what the
/// module never observed (`docs/module-interface-cutoff-design.md` §2).
/// Advisory: a wrong record can make a relocation fail its replay or be
/// refused, and the relocated delta is kernel-rechecked like any image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorldRecord {
    /// The dependency prefix's length: the base the image's positions count
    /// from.
    pub base: u64,
    /// The world's modules, in load order.
    pub modules: Vec<String>,
    /// Every dependency binding the image refers to, by content.
    pub references: Vec<WorldReference>,
    /// Digest of the world's registries: every module with registry events,
    /// its projection with positions replaced by content.
    pub registry: [u8; 32],
    /// Names the elaboration looked up that its source does not spell (an
    /// operator's fallback name, a tactic's lemma), by last `::` segment.
    pub lookups: Vec<String>,
    /// Digest of what the module's identifiers and [`Self::lookups`] resolve
    /// to in the world.
    pub names: [u8; 32],
}

/// One dependency binding an image refers to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorldReference {
    /// Its position in the old world.
    pub abs: u64,
    /// Its module, an index into [`WorldRecord::modules`].
    pub module: u32,
    /// Its content identity (`merkle::interface_hash`).
    pub hash: [u8; 32],
    /// Which of the module's bindings with this identity it is, counting
    /// from the first; and how many there were.
    pub rank: u32,
    pub count: u32,
}

impl WorldRecord {
    fn encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.base.to_le_bytes());
        out.extend_from_slice(&(self.modules.len() as u64).to_le_bytes());
        for module in &self.modules {
            out.extend_from_slice(&(module.len() as u64).to_le_bytes());
            out.extend_from_slice(module.as_bytes());
        }
        out.extend_from_slice(&(self.references.len() as u64).to_le_bytes());
        for r in &self.references {
            out.extend_from_slice(&r.abs.to_le_bytes());
            out.extend_from_slice(&r.module.to_le_bytes());
            out.extend_from_slice(&r.hash);
            out.extend_from_slice(&r.rank.to_le_bytes());
            out.extend_from_slice(&r.count.to_le_bytes());
        }
        out.extend_from_slice(&(self.lookups.len() as u64).to_le_bytes());
        for name in &self.lookups {
            out.extend_from_slice(&(name.len() as u64).to_le_bytes());
            out.extend_from_slice(name.as_bytes());
        }
        out.extend_from_slice(&self.registry);
        out.extend_from_slice(&self.names);
    }

    fn decode(bytes: &[u8], limits: ModuleImageLimits) -> Result<Self, ModuleCacheError> {
        let corrupt = ModuleCacheError::Corrupt("module world record is malformed");
        let mut at = 0;
        let mut take = |n: usize| -> Result<&[u8], ModuleCacheError> {
            let end = at + n;
            if end > bytes.len() {
                return Err(ModuleCacheError::Corrupt("module world record is malformed"));
            }
            let out = &bytes[at..end];
            at = end;
            Ok(out)
        };
        let base = u64::from_le_bytes(take(8)?.try_into().unwrap());
        let count = u64::from_le_bytes(take(8)?.try_into().unwrap()) as usize;
        if count > limits.max_sequence {
            return Err(corrupt);
        }
        let mut modules = Vec::with_capacity(count);
        for _ in 0..count {
            let len = u64::from_le_bytes(take(8)?.try_into().unwrap()) as usize;
            if len > limits.max_string_bytes {
                return Err(ModuleCacheError::Corrupt("module world record is malformed"));
            }
            let name = std::str::from_utf8(take(len)?)
                .map_err(|_| ModuleCacheError::Corrupt("module world record is malformed"))?;
            modules.push(name.to_string());
        }
        let count = u64::from_le_bytes(take(8)?.try_into().unwrap()) as usize;
        if count > limits.max_sequence {
            return Err(ModuleCacheError::Corrupt("module world record is malformed"));
        }
        let mut references = Vec::with_capacity(count);
        for _ in 0..count {
            let abs = u64::from_le_bytes(take(8)?.try_into().unwrap());
            let module = u32::from_le_bytes(take(4)?.try_into().unwrap());
            let hash: [u8; 32] = take(32)?.try_into().unwrap();
            let rank = u32::from_le_bytes(take(4)?.try_into().unwrap());
            let count = u32::from_le_bytes(take(4)?.try_into().unwrap());
            if module as usize >= modules.len() || rank >= count || abs >= base {
                return Err(ModuleCacheError::Corrupt("module world record is malformed"));
            }
            references.push(WorldReference { abs, module, hash, rank, count });
        }
        let count = u64::from_le_bytes(take(8)?.try_into().unwrap()) as usize;
        if count > limits.max_sequence {
            return Err(ModuleCacheError::Corrupt("module world record is malformed"));
        }
        let mut lookups = Vec::with_capacity(count);
        for _ in 0..count {
            let len = u64::from_le_bytes(take(8)?.try_into().unwrap()) as usize;
            if len > limits.max_string_bytes {
                return Err(ModuleCacheError::Corrupt("module world record is malformed"));
            }
            let name = std::str::from_utf8(take(len)?)
                .map_err(|_| ModuleCacheError::Corrupt("module world record is malformed"))?;
            lookups.push(name.to_string());
        }
        let registry: [u8; 32] = take(32)?.try_into().unwrap();
        let names: [u8; 32] = take(32)?.try_into().unwrap();
        if at != bytes.len() {
            return Err(ModuleCacheError::Corrupt("module world record has trailing bytes"));
        }
        Ok(Self { base, modules, references, lookups, registry, names })
    }
}

fn put_bytes(h: &mut Sha256, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

pub struct LoadedModule {
    pub delta: ModuleDelta,
    pub warnings: Vec<Warning>,
    /// The build that wrote the image when it is not this one. `None` for
    /// an image of the current build; only [`ImageFreshness::AcceptStale`]
    /// ever loads a `Some`.
    pub stale: Option<SemanticsIdentity>,
    /// V1 conservatively identifies the complete semantic artifact. A later
    /// interface projection can stop proof-only edits invalidating consumers
    /// without changing the loader/storage boundary.
    pub interface_hash: [u8; 32],
    /// What the image recorded about its dependency world, when its writer
    /// could say (`docs/module-interface-cutoff-design.md` §2).
    pub world: Option<WorldRecord>,
    /// Declarations the module's `expect-error` directives say are refused,
    /// and its writer saw refused that way; zero for a module that checked
    /// whole. The delta holds the module's other items
    /// (`docs/module-dag-design.md` §11).
    pub refusals: usize,
}

#[derive(Debug)]
pub enum ModuleCacheError {
    Io(std::io::Error),
    Corrupt(&'static str),
    Decode(ModuleImageDecodeError),
    /// The image would be refused by its own reader, so it was not written:
    /// a stored over-budget image is decoded up to the budget, rejected and
    /// re-published on every warm run
    /// (`issues/semantic-image-over-budget-republished-every-run.md`).
    OverBudget { nodes: u64, limit: u64 },
}

impl fmt::Display for ModuleCacheError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => write!(f, "{e}"),
            Self::Corrupt(why) => write!(f, "{why}"),
            Self::Decode(e) => write!(f, "semantic image was rejected: {e}"),
            Self::OverBudget { nodes, limit } => write!(
                f,
                "semantic image has {nodes} syntax nodes, past the decode budget of {limit}; not stored, so a warm run re-elaborates this module"
            ),
        }
    }
}

impl std::error::Error for ModuleCacheError {}

/// A publish the store declined on size, recorded beside the `.latest`
/// pointer so a later `--only` can say so with the number
/// (`issues/check-only-no-stored-image.md`).
///
/// Advisory only — see [`ModuleImageCache::refusal_path`]. The wire form is
/// one line of ASCII so an unknown future variant reads back as `None`
/// rather than as a wrong number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImageRefusal {
    /// Past the reader's node budget: the `--only` case this exists for.
    Nodes { nodes: u64, limit: u64 },
    /// Past the byte limit. The same user-visible situation, a different
    /// rail, and a message that must not quote a node count it does not have.
    Bytes { bytes: u64, limit: u64 },
}

impl ImageRefusal {
    fn encode(self) -> String {
        match self {
            Self::Nodes { nodes, limit } => format!("v1 nodes {nodes} {limit}\n"),
            Self::Bytes { bytes, limit } => format!("v1 bytes {bytes} {limit}\n"),
        }
    }

    fn parse(line: &str) -> Option<Self> {
        let mut fields = line.split_whitespace();
        if fields.next()? != "v1" {
            return None;
        }
        let kind = fields.next()?;
        let measured: u64 = fields.next()?.parse().ok()?;
        let limit: u64 = fields.next()?.parse().ok()?;
        match kind {
            "nodes" => Some(Self::Nodes { nodes: measured, limit }),
            "bytes" => Some(Self::Bytes { bytes: measured, limit }),
            _ => None,
        }
    }
}

impl fmt::Display for ImageRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nodes { nodes, limit } => {
                write!(f, "its image has {nodes} syntax nodes, past the decode budget of {limit}")
            }
            Self::Bytes { bytes, limit } => {
                write!(f, "its image is {bytes} bytes, past the store's limit of {limit}")
            }
        }
    }
}

impl From<std::io::Error> for ModuleCacheError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

/// How many bytes of published images the store keeps, beyond the ones a
/// `.latest` pointer names — which are never evicted, since they are what an
/// edited module replays its unchanged declarations from.
///
/// Measured on this repo's own store on 2026-09-19, before there was any
/// retention at all: 3,625 images, 9.2 GiB, of which **116 (0.33 GiB) were
/// named by a pointer and 3,509 (8.85 GiB) were named by nothing**. The
/// unreferenced ones are not garbage — an image is addressed by a content key,
/// so checking out an older tree finds its image again — but the store was
/// growing without bound on a filesystem that has filled before
/// (issues/showcase-harness.md). The budget is what that history costs.
pub const DEFAULT_RETAIN_BYTES: u64 = 4 << 30;

pub struct ModuleImageCache {
    dir: PathBuf,
    limits: ModuleImageLimits,
    retain_bytes: u64,
}

impl ModuleImageCache {
    pub fn new(cache_dir: PathBuf) -> Self {
        Self {
            dir: cache_dir.join("modules-v1"),
            limits: ModuleImageLimits::default(),
            retain_bytes: DEFAULT_RETAIN_BYTES,
        }
    }

    pub fn with_limits(cache_dir: PathBuf, limits: ModuleImageLimits) -> Self {
        Self {
            dir: cache_dir.join("modules-v1"),
            limits,
            retain_bytes: DEFAULT_RETAIN_BYTES,
        }
    }

    /// The retention budget, for a caller that wants a smaller store (or a
    /// test that wants to see eviction happen without writing 4 GiB).
    pub fn with_retention(mut self, retain_bytes: u64) -> Self {
        self.retain_bytes = retain_bytes;
        self
    }

    /// Evict published images, oldest first, until the store fits its budget.
    ///
    /// Never evicts an image a `.latest` pointer names: those are the replay
    /// set, and losing one costs a full re-elaboration rather than a slice.
    /// Everything else is a content-addressed hit for some older tree, which
    /// is worth keeping until it is worth more than the disk.
    ///
    /// Best-effort by construction. A concurrent run may publish between the
    /// listing and the unlink, and an image this sweep removes may be one
    /// another process was about to load: both outcomes are an ordinary cache
    /// miss, which the reader already handles by rebuilding. Nothing here can
    /// produce a wrong answer, only a slower run.
    fn sweep(&self) {
        let Ok(entries) = std::fs::read_dir(&self.dir) else { return };
        let mut pinned: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut images: Vec<(std::time::SystemTime, u64, PathBuf, String)> = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(stem) = path.file_stem().and_then(|s| s.to_str()).map(str::to_string) else {
                continue;
            };
            match path.extension().and_then(|e| e.to_str()) {
                Some("latest") => {
                    if let Ok(bytes) = std::fs::read(&path) {
                        if let Ok(key) = <[u8; 32]>::try_from(bytes.as_slice()) {
                            pinned.insert(hex(&key));
                        }
                    }
                }
                Some("hmi") => {
                    if let Ok(meta) = entry.metadata() {
                        let when = meta.modified().unwrap_or(std::time::SystemTime::UNIX_EPOCH);
                        images.push((when, meta.len(), path, stem));
                    }
                }
                _ => {}
            }
        }
        let mut total: u64 = images.iter().map(|(_, len, _, _)| *len).sum();
        if total <= self.retain_bytes {
            return;
        }
        // Oldest first; a pinned image is skipped rather than counted out, so
        // a store whose pointers alone exceed the budget shrinks to them and
        // stops, instead of evicting the replay set it exists to serve.
        images.sort_by_key(|(when, _, _, _)| *when);
        for (_, len, path, stem) in images {
            if total <= self.retain_bytes {
                break;
            }
            if pinned.contains(&stem) {
                continue;
            }
            if std::fs::remove_file(&path).is_ok() {
                total = total.saturating_sub(len);
            }
        }
    }

    pub fn path(&self, key: ModuleCacheKey) -> PathBuf {
        self.dir.join(format!("{}.hmi", hex(&key.0)))
    }

    /// The pointer to the newest image published for `module` over
    /// `dependencies`, whatever its source: what an edited module replays
    /// its unchanged declarations from
    /// (`docs/declaration-slice-replay-design.md` §4). One small file per
    /// (module, dependency world), holding the image's cache key.
    fn latest_path(&self, module: &str, dependencies: &ModuleDependencyIdentity) -> PathBuf {
        self.dir.join(format!("{}.latest", self.world_key(module, dependencies)))
    }

    /// The refusal marker beside [`Self::latest_path`], same (module,
    /// dependency world) key: what the store writes *instead of* a pointer
    /// when it declines an image as over budget
    /// (`issues/check-only-no-stored-image.md`).
    ///
    /// **It is not part of the image or verdict contract.** Nothing decodes
    /// it, nothing keys a hit on it, `load`/`load_previous`/`sweep` do not
    /// consult it, and a lost or corrupt marker costs exactly one less
    /// helpful diagnostic. It exists so `--only` can quote the size at the
    /// run that fails instead of asking the reader to remember an earlier
    /// run's notice.
    fn refusal_path(&self, module: &str, dependencies: &ModuleDependencyIdentity) -> PathBuf {
        self.dir.join(format!("{}.refused", self.world_key(module, dependencies)))
    }

    /// The pointer to the newest image published for a module's exact source
    /// over any dependency world: a relocation candidate
    /// (`docs/module-interface-cutoff-design.md` §2). Like `.latest`, one
    /// small file holding a cache key; unlike it, never a pin.
    fn source_path(&self, source: SourceKey) -> PathBuf {
        self.dir.join(format!("{}.src", hex(&source.0)))
    }

    /// The newest image of this exact source over whatever world it was
    /// elaborated over, decoded against a stand-in prefix of the right
    /// length (relocation replaces it), under the same freshness policy as
    /// [`Self::load`]. `None` when there is none, or it carries no world
    /// record. The stand-in means the delta is only good for
    /// `ModuleDelta::relocate`: replaying it as it is would fail the
    /// dependency checks, as it should.
    pub fn load_candidate(
        &self,
        source: SourceKey,
        source_len: usize,
        freshness: ImageFreshness,
    ) -> Result<Option<LoadedModule>, ModuleCacheError> {
        let pointer = match std::fs::read(self.source_path(source)) {
            Ok(bytes) => bytes,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.into()),
        };
        let Ok(key) = <[u8; 32]>::try_from(pointer.as_slice()) else {
            return Err(ModuleCacheError::Corrupt("module source pointer has the wrong length"));
        };
        let Some(base) = self.peek_world_base(ModuleCacheKey(key))? else {
            return Ok(None);
        };
        let base = usize::try_from(base)
            .ok()
            .filter(|base| *base <= self.limits.max_sequence.saturating_mul(64))
            .ok_or(ModuleCacheError::Corrupt("module world record base is implausible"))?;
        let stand_in = GlobalCtx::new(vec![heather_kernel::term::GlobalBinding::Ctx; base]);
        self.load(ModuleCacheKey(key), stand_in, source_len, freshness)
    }

    /// The world record's base, read without decoding the image: what the
    /// stand-in prefix of [`Self::load_candidate`] must be as long as.
    fn peek_world_base(&self, key: ModuleCacheKey) -> Result<Option<u64>, ModuleCacheError> {
        let mut head = [0u8; HEADER + 9];
        let mut file = match std::fs::File::open(self.path(key)) {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.into()),
        };
        use std::io::{Seek, SeekFrom};
        if file.read_exact(&mut head[..HEADER]).is_err() || &head[..8] != MAGIC {
            return Ok(None);
        }
        let semantic_len = u64::from_le_bytes(head[104..112].try_into().unwrap());
        let world_len = u64::from_le_bytes(head[120..128].try_into().unwrap());
        if world_len < 9 {
            return Ok(None);
        }
        file.seek(SeekFrom::Start(HEADER as u64 + semantic_len))?;
        let mut flag_and_base = [0u8; 9];
        if file.read_exact(&mut flag_and_base).is_err() || flag_and_base[0] != 1 {
            return Ok(None);
        }
        Ok(Some(u64::from_le_bytes(flag_and_base[1..9].try_into().unwrap())))
    }

    fn world_key(&self, module: &str, dependencies: &ModuleDependencyIdentity) -> String {
        let mut h = Sha256::new();
        h.update(b"heather-module-latest-v1\0");
        put_bytes(&mut h, module.as_bytes());
        h.update(&(dependencies.ordered_interface_hashes().len() as u64).to_le_bytes());
        for dependency in dependencies.ordered_interface_hashes() {
            h.update(dependency);
        }
        hex(&h.finish())
    }

    /// Why the store last declined to publish this module over this
    /// dependency world, if it did and no publish has succeeded since.
    /// Best-effort and advisory: `None` means "no marker", never "the image
    /// fits".
    pub fn refusal(
        &self,
        module: &str,
        dependencies: &ModuleDependencyIdentity,
    ) -> Option<ImageRefusal> {
        let text = std::fs::read_to_string(self.refusal_path(module, dependencies)).ok()?;
        ImageRefusal::parse(text.trim())
    }

    /// Record (or clear) the marker. Every failure is swallowed: a store that
    /// cannot write a diagnostic file still published, or still refused, and
    /// the caller's own result is the answer.
    fn note_refusal(
        &self,
        module: &str,
        dependencies: &ModuleDependencyIdentity,
        refusal: Option<ImageRefusal>,
    ) {
        let path = self.refusal_path(module, dependencies);
        match refusal {
            Some(refusal) => {
                // The refusal is reached before `publish_as` creates the
                // store directory, so the marker is the first thing a store
                // that has never published anything writes.
                let _ = std::fs::create_dir_all(&self.dir);
                let temp = temporary_sibling(&path);
                if std::fs::write(&temp, refusal.encode())
                    .and_then(|()| std::fs::rename(&temp, &path))
                    .is_err()
                {
                    let _ = std::fs::remove_file(&temp);
                }
            }
            None => {
                let _ = std::fs::remove_file(&path);
            }
        }
    }

    /// The newest image of `module` over `dependencies`, under the same
    /// freshness policy as [`Self::load`]; `None` when no image was ever
    /// published for that world or the pointer's target is gone. Its
    /// warnings are attached to the delta so its slices can replay. The
    /// warning spans are not bounded by any source length here: they refer
    /// to the source that image was built from and are relocated before use.
    pub fn load_previous(
        &self,
        module: &str,
        dependencies: &ModuleDependencyIdentity,
        dependency_psi: GlobalCtx,
        freshness: ImageFreshness,
    ) -> Result<Option<LoadedModule>, ModuleCacheError> {
        let pointer = match std::fs::read(self.latest_path(module, dependencies)) {
            Ok(bytes) => bytes,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.into()),
        };
        let Ok(key) = <[u8; 32]>::try_from(pointer.as_slice()) else {
            return Err(ModuleCacheError::Corrupt("module latest-image pointer has the wrong length"));
        };
        let Some(mut loaded) = self.load(ModuleCacheKey(key), dependency_psi, usize::MAX, freshness)? else {
            return Ok(None);
        };
        if loaded.delta.module() != module {
            return Err(ModuleCacheError::Corrupt("module latest-image pointer names another module"));
        }
        loaded.delta = loaded
            .delta
            .with_warnings(loaded.warnings.clone())
            .map_err(ModuleCacheError::Corrupt)?;
        Ok(Some(loaded))
    }

    pub fn interface_hash(delta: &ModuleDelta) -> [u8; 32] {
        projected_interface(delta)
    }

    /// Absence is an ordinary miss, and so — under [`ImageFreshness::Exact`]
    /// — is an image another build wrote. An existing but unusable artifact
    /// is distinguished so callers can report corruption before rebuilding.
    pub fn load(
        &self,
        key: ModuleCacheKey,
        dependency_psi: GlobalCtx,
        source_len: usize,
        freshness: ImageFreshness,
    ) -> Result<Option<LoadedModule>, ModuleCacheError> {
        let path = self.path(key);
        let file = match std::fs::File::open(&path) {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.into()),
        };
        let max_file = self.limits.max_bytes.saturating_add(HEADER + CHECKSUM);
        // A metadata preflight alone has a TOCTOU hole: the file can grow
        // before the read. Cap the read itself and reject the sentinel byte.
        let mut bytes = Vec::new();
        file.take(max_file.saturating_add(1) as u64)
            .read_to_end(&mut bytes)?;
        if bytes.len() > max_file {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact exceeds the byte limit",
            ));
        }
        if bytes.len() < HEADER + CHECKSUM || &bytes[..8] != MAGIC {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact has an invalid header",
            ));
        }
        if bytes[8..40] != key.0 {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact has the wrong cache key",
            ));
        }
        let mut semantics = [0; 32];
        semantics.copy_from_slice(&bytes[40..72]);
        let semantics = SemanticsIdentity(semantics);
        let stale = match freshness {
            _ if semantics == SemanticsIdentity::current() => None,
            ImageFreshness::Exact => return Ok(None),
            ImageFreshness::AcceptStale => Some(semantics),
        };
        let mut interface_hash = [0; 32];
        interface_hash.copy_from_slice(&bytes[72..104]);
        let semantic_len = u64::from_le_bytes(bytes[104..112].try_into().unwrap());
        let semantic_len = usize::try_from(semantic_len)
            .map_err(|_| ModuleCacheError::Corrupt("module cache artifact length overflows"))?;
        let warning_count = u64::from_le_bytes(bytes[112..120].try_into().unwrap());
        let warning_count = usize::try_from(warning_count)
            .map_err(|_| ModuleCacheError::Corrupt("module warning count overflows"))?;
        if warning_count > self.limits.max_sequence {
            return Err(ModuleCacheError::Corrupt("module warning count exceeds the limit"));
        }
        let world_len = u64::from_le_bytes(bytes[120..128].try_into().unwrap());
        let refusals = u64::from_le_bytes(bytes[128..136].try_into().unwrap());
        let refusals = usize::try_from(refusals)
            .map_err(|_| ModuleCacheError::Corrupt("module refusal count overflows"))?;
        let world_len = usize::try_from(world_len)
            .map_err(|_| ModuleCacheError::Corrupt("module world record length overflows"))?;
        let semantic_end = HEADER
            .checked_add(semantic_len)
            .ok_or(ModuleCacheError::Corrupt(
                "module cache artifact length overflows",
            ))?;
        let world_end = semantic_end
            .checked_add(world_len)
            .ok_or(ModuleCacheError::Corrupt("module cache artifact length overflows"))?;
        let checksum_at = bytes.len() - CHECKSUM;
        if world_end > checksum_at {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact length does not match",
            ));
        }
        if sha256(&bytes[..checksum_at]) != bytes[checksum_at..] {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact checksum does not match",
            ));
        }
        let semantic = &bytes[HEADER..semantic_end];
        let delta = ModuleDelta::from_image_bytes(semantic, dependency_psi, self.limits)
            .map_err(ModuleCacheError::Decode)?;
        // The stored interface hash is the writer's projection. A different
        // build may project differently (that is what its fingerprint says),
        // so under `AcceptStale` the reader's own projection is the identity
        // that downstream keys must chain from; a mismatch is corruption
        // only when the writer was this build.
        let projected = projected_interface(&delta);
        if projected != interface_hash {
            if stale.is_none() {
                return Err(ModuleCacheError::Corrupt(
                    "module cache interface identity does not match",
                ));
            }
            interface_hash = projected;
        }
        let world = match bytes.get(semantic_end) {
            Some(1) if world_len > 0 => {
                Some(WorldRecord::decode(&bytes[semantic_end + 1..world_end], self.limits)?)
            }
            _ => None,
        };
        let warnings = decode_warnings(
            &bytes[world_end..checksum_at],
            warning_count,
            source_len,
            self.limits,
        )?;
        Ok(Some(LoadedModule {
            delta,
            warnings,
            stale,
            interface_hash,
            world,
            refusals,
        }))
    }

    /// Take the build lock for `key`, blocking while another process holds
    /// it: the single flight a miss goes through before elaborating, so that
    /// processes missing the same key at once build it once rather than each
    /// (`issues/testing-architecture.md`: on a fresh store the suite spent
    /// about as much again as the one-each floor on such repeats). The
    /// caller loads again once it holds the lock, since the holder it waited
    /// on has usually just published, and keeps the lock until its own
    /// publication.
    ///
    /// Advisory and best-effort. The lock is an OS file lock, released when
    /// the holder drops it or dies (a test killed at the CPU rail cannot
    /// strand its waiters), and an error taking it is `None`: the caller
    /// builds unlocked, as every caller did before. Correctness never rests
    /// on it — two builders of one key publish the same content by atomic
    /// rename. The lock files stay: unlinking one while another process
    /// waits on it would let a third lock a fresh inode beside it. That is one
    /// empty file per key built; the retention sweep leaves them alone.
    pub fn build_lock(&self, key: ModuleCacheKey) -> Option<std::fs::File> {
        std::fs::create_dir_all(&self.dir).ok()?;
        let path = self.dir.join(format!("{}.lock", hex(&key.0)));
        let file = std::fs::OpenOptions::new().create(true).truncate(false).write(true).open(path).ok()?;
        file.lock().ok()?;
        Some(file)
    }

    /// Whether another process is building `key` now: no image yet, and its
    /// build lock is held. A scheduler sets such a module aside and checks
    /// another whose imports it has, rather than wait
    /// (`docs/module-dag-design.md` §7). Advisory, like the lock: `false`
    /// when it cannot tell.
    pub fn being_built(&self, key: ModuleCacheKey) -> bool {
        if self.path(key).exists() {
            return false;
        }
        let path = self.dir.join(format!("{}.lock", hex(&key.0)));
        let Ok(file) = std::fs::OpenOptions::new().write(true).open(path) else { return false };
        matches!(file.try_lock(), Err(std::fs::TryLockError::WouldBlock))
    }

    /// Publish through a unique temporary sibling and atomic rename. Leaving
    /// a temporary file after a crash is harmless: readers name only the
    /// content-addressed final path.
    pub fn publish(
        &self,
        key: ModuleCacheKey,
        delta: &ModuleDelta,
        warnings: &[Warning],
    ) -> Result<[u8; 32], ModuleCacheError> {
        self.publish_as(key, delta, warnings, SemanticsIdentity::current())
    }

    /// [`Self::publish`] on behalf of another build. Tests use it to stage the
    /// image a previous compiler would have left behind; nothing else should.
    pub fn publish_as(
        &self,
        key: ModuleCacheKey,
        delta: &ModuleDelta,
        warnings: &[Warning],
        semantics: SemanticsIdentity,
    ) -> Result<[u8; 32], ModuleCacheError> {
        self.publish_world(key, delta, warnings, semantics, None)
    }

    /// [`Self::publish_as`] with the module's world record and source key,
    /// so a later run over another world can find the image by its source and
    /// move it (`docs/module-interface-cutoff-design.md` §2). The source
    /// pointer is written only with a record: an image without one cannot be
    /// moved.
    pub fn publish_world(
        &self,
        key: ModuleCacheKey,
        delta: &ModuleDelta,
        warnings: &[Warning],
        semantics: SemanticsIdentity,
        world: Option<(SourceKey, &WorldRecord)>,
    ) -> Result<[u8; 32], ModuleCacheError> {
        self.publish_refused(key, delta, warnings, semantics, world, 0)
    }

    /// [`Self::publish_world`] for a module `refusals` of whose declarations
    /// were refused as its directives say: `delta` is the rest of it.
    pub fn publish_refused(
        &self,
        key: ModuleCacheKey,
        delta: &ModuleDelta,
        warnings: &[Warning],
        semantics: SemanticsIdentity,
        world: Option<(SourceKey, &WorldRecord)>,
        refusals: usize,
    ) -> Result<[u8; 32], ModuleCacheError> {
        let (semantic, nodes) = delta.to_image();
        if nodes > self.limits.max_nodes {
            self.note_refusal(
                delta.module(),
                delta.dependencies(),
                Some(ImageRefusal::Nodes { nodes, limit: self.limits.max_nodes }),
            );
            return Err(ModuleCacheError::OverBudget { nodes, limit: self.limits.max_nodes });
        }
        if semantic.len() > self.limits.max_bytes {
            self.note_refusal(
                delta.module(),
                delta.dependencies(),
                Some(ImageRefusal::Bytes {
                    bytes: semantic.len() as u64,
                    limit: self.limits.max_bytes as u64,
                }),
            );
            return Err(ModuleCacheError::Corrupt(
                "semantic image exceeds the byte limit",
            ));
        }
        let interface_hash = projected_interface(delta);
        if warnings.len() > self.limits.max_sequence {
            return Err(ModuleCacheError::Corrupt("module warning count exceeds the limit"));
        }
        let mut record = Vec::new();
        if let Some((_, world)) = world {
            record.push(1);
            world.encode(&mut record);
        }
        let mut bytes = Vec::with_capacity(HEADER + semantic.len() + record.len() + CHECKSUM);
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(&key.0);
        bytes.extend_from_slice(&semantics.0);
        bytes.extend_from_slice(&interface_hash);
        bytes.extend_from_slice(&(semantic.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&(warnings.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&(record.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&(refusals as u64).to_le_bytes());
        bytes.extend_from_slice(&semantic);
        bytes.extend_from_slice(&record);
        encode_warnings(&mut bytes, warnings, self.limits)?;
        if bytes.len() > HEADER.saturating_add(self.limits.max_bytes) {
            return Err(ModuleCacheError::Corrupt("module cache artifact exceeds the byte limit"));
        }
        let checksum = sha256(&bytes);
        bytes.extend_from_slice(&checksum);

        std::fs::create_dir_all(&self.dir)?;
        let final_path = self.path(key);
        let temp_path = temporary_sibling(&final_path);
        if let Err(error) = std::fs::write(&temp_path, bytes)
            .and_then(|()| std::fs::rename(&temp_path, &final_path))
        {
            let _ = std::fs::remove_file(&temp_path);
            return Err(error.into());
        }
        // The newest-image pointer, last: a reader that finds it finds the
        // image. Losing the pointer costs one un-sliced edit check, never a
        // wrong answer.
        let latest = self.latest_path(delta.module(), delta.dependencies());
        let temp_latest = temporary_sibling(&latest);
        if let Err(error) = std::fs::write(&temp_latest, key.0)
            .and_then(|()| std::fs::rename(&temp_latest, &latest))
        {
            let _ = std::fs::remove_file(&temp_latest);
            return Err(error.into());
        }
        // The source pointer, for a relocation from another world. Best
        // effort like the rest: a lost pointer is one more elaboration.
        if let Some((source, _)) = world {
            let pointer = self.source_path(source);
            let temp = temporary_sibling(&pointer);
            if std::fs::write(&temp, key.0).and_then(|()| std::fs::rename(&temp, &pointer)).is_err() {
                let _ = std::fs::remove_file(&temp);
            }
        }
        // A world that now has a pointer has no refusal: an image that fits
        // must not leave a stale marker behind to mislead the next `--only`.
        self.note_refusal(delta.module(), delta.dependencies(), None);
        self.sweep();
        Ok(interface_hash)
    }
}

fn encode_warnings(
    out: &mut Vec<u8>,
    warnings: &[Warning],
    limits: ModuleImageLimits,
) -> Result<(), ModuleCacheError> {
    for warning in warnings {
        out.push(match warning.lint {
            Lint::UnreachableMatchArm => 0,
            Lint::MatchFunctionApplication => 1,
            Lint::StdlibUnicodeSpelling => 3,
            Lint::NestedCall => 4,
            Lint::UnusedPatternBinder => 5,
            Lint::OperatorFallback => 6,
            Lint::RedundantMatchMotive => 7,
            Lint::ManualListConstruction => 8,
            Lint::RecursionByMeasure => 9,
            Lint::InexactLiteral => 10,
        });
        put_warning_string(out, &warning.msg, limits)?;
        put_span(out, warning.span);
        match &warning.fix {
            None => out.push(0),
            Some(fix) => {
                out.push(1);
                put_span(out, fix.span);
                put_warning_string(out, &fix.replacement, limits)?;
            }
        }
    }
    Ok(())
}

fn put_warning_string(
    out: &mut Vec<u8>,
    value: &str,
    limits: ModuleImageLimits,
) -> Result<(), ModuleCacheError> {
    if value.len() > limits.max_string_bytes {
        return Err(ModuleCacheError::Corrupt("module warning string exceeds the limit"));
    }
    out.extend_from_slice(&(value.len() as u64).to_le_bytes());
    out.extend_from_slice(value.as_bytes());
    Ok(())
}

fn put_span(out: &mut Vec<u8>, span: Span) {
    out.extend_from_slice(&(span.start as u64).to_le_bytes());
    out.extend_from_slice(&(span.end as u64).to_le_bytes());
}

fn decode_warnings(
    bytes: &[u8],
    count: usize,
    source_len: usize,
    limits: ModuleImageLimits,
) -> Result<Vec<Warning>, ModuleCacheError> {
    let mut reader = WarningReader { bytes, at: 0, source_len, limits };
    let mut warnings = Vec::with_capacity(count);
    for _ in 0..count {
        let lint = match reader.byte()? {
            0 => Lint::UnreachableMatchArm,
            1 => Lint::MatchFunctionApplication,
            3 => Lint::StdlibUnicodeSpelling,
            4 => Lint::NestedCall,
            5 => Lint::UnusedPatternBinder,
            6 => Lint::OperatorFallback,
            7 => Lint::RedundantMatchMotive,
            8 => Lint::ManualListConstruction,
            9 => Lint::RecursionByMeasure,
            10 => Lint::InexactLiteral,
            _ => return Err(ModuleCacheError::Corrupt("module warning has an invalid lint tag")),
        };
        let msg = reader.string()?;
        let span = reader.span()?;
        let fix = match reader.byte()? {
            0 => None,
            1 => Some(LintFix { span: reader.span()?, replacement: reader.string()? }),
            _ => return Err(ModuleCacheError::Corrupt("module warning has an invalid fix tag")),
        };
        warnings.push(Warning { lint, msg, span, fix });
    }
    if reader.at != bytes.len() {
        return Err(ModuleCacheError::Corrupt("module warning payload has trailing bytes"));
    }
    Ok(warnings)
}

struct WarningReader<'a> {
    bytes: &'a [u8],
    at: usize,
    source_len: usize,
    limits: ModuleImageLimits,
}

impl WarningReader<'_> {
    fn take(&mut self, len: usize) -> Result<&[u8], ModuleCacheError> {
        let end = self
            .at
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(ModuleCacheError::Corrupt("module warning payload is truncated"))?;
        let value = &self.bytes[self.at..end];
        self.at = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, ModuleCacheError> {
        Ok(self.take(1)?[0])
    }

    fn usize(&mut self) -> Result<usize, ModuleCacheError> {
        let value = u64::from_le_bytes(self.take(8)?.try_into().unwrap());
        usize::try_from(value)
            .map_err(|_| ModuleCacheError::Corrupt("module warning integer overflows"))
    }

    fn string(&mut self) -> Result<String, ModuleCacheError> {
        let len = self.usize()?;
        if len > self.limits.max_string_bytes {
            return Err(ModuleCacheError::Corrupt("module warning string exceeds the limit"));
        }
        let bytes = self.take(len)?;
        let value = std::str::from_utf8(bytes)
            .map_err(|_| ModuleCacheError::Corrupt("module warning string is not UTF-8"))?;
        Ok(value.to_string())
    }

    fn span(&mut self) -> Result<Span, ModuleCacheError> {
        let start = self.usize()?;
        let end = self.usize()?;
        if start > end || end > self.source_len {
            return Err(ModuleCacheError::Corrupt("module warning span is outside its source"));
        }
        Ok(Span { start, end })
    }
}

fn projected_interface(delta: &ModuleDelta) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(DOMAIN_INTERFACE);
    h.update(&delta.to_interface_bytes());
    h.finish()
}

fn temporary_sibling(path: &Path) -> PathBuf {
    let id = TEMP_ID.fetch_add(1, Ordering::Relaxed);
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("module.hmi");
    path.with_file_name(format!(".{name}.{}.{}.tmp", std::process::id(), id))
}
