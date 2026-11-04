//! The declaration cache: content-addressed, kernel-gate-skipping, rung 1.
//!
//! Design: `docs/cache-v1-design.md`. Architecture and everything not in v1:
//! `issues/parallel-checking-and-caching.md`.
//!
//! What it does, in one sentence: it watches the two kernel-gate sites through
//! `heather_elab::gate`, gives every declaration a hash of its elaborated form
//! with global references replaced by the hashes of their referents, and lets
//! the elaborator skip the gate for hashes a previous run recorded as
//! accepted.
//!
//! What it does **not** do is skip parsing or elaboration; a warm run pays
//! those in full (`docs/cache-v1-design.md` §1). And it lives above the
//! kernel, never inside it: the kernel stays at zero dependencies and knows
//! nothing about any of this.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use heather_elab::gate::{GateItem, KernelGate};
use heather_kernel::term::GlobalCtx;

pub mod merkle;
pub mod module_image;
pub mod sha256;
pub mod store;

use merkle::Hash;
use store::Store;

/// A fingerprint of the kernel's source, computed by `build.rs` over
/// `crates/kernel/src` and compiled in.
///
/// This is v1's **kernel-semantics fingerprint** (`docs/cache-v1-design.md`
/// §6). It is deliberately conservative — a comment in the kernel invalidates
/// every entry — because erring that way is free and the other way is a
/// wrongly accepted proof, and because deriving it from the build makes
/// "a changed kernel invalidates loudly" a property of the build rather than
/// of someone remembering to bump a constant.
///
/// What it should become: a fingerprint of the kernel's *semantics* — the
/// conversion rules, the strip discipline, the layer table — so a pure
/// performance round does not invalidate a corpus. Same distinction as the
/// issue's "decisions, not steps" trace rule, and it should end up being the
/// same value.
pub const KERNEL_SEMANTICS: &str = env!("HEATHER_KERNEL_SEMANTICS");

/// Conservative build-derived identity for the parser, elaborator, image
/// schema producer, and kernel used by persistent semantic module images.
pub const ELABORATOR_SEMANTICS: &str = env!("HEATHER_ELABORATOR_SEMANTICS");

/// The per-repository cache directory, relative to the working directory.
pub const DEFAULT_DIR: &str = ".heather/cache";

/// Names a directory to hold every cache this checkout's tools and suites
/// keep, in place of their defaults. For several checkouts of one repository
/// (git worktrees, one per agent) that should share what they can: every
/// store below is content-addressed, and every replay is kernel-rechecked or
/// vouched for under the reader's own kernel (`docs/cache-v1-design.md`), so a
/// shared store can cost a miss but never a wrong answer. A relative value is
/// taken from the repository root (from the working directory for
/// [`default_dir`]); set it absolute.
pub const CACHE_DIR_ENV: &str = "HEATHER_CACHE_DIR";

/// The stores the suites and gates share, by name beneath [`store_root`].
pub const SEMANTIC_TEST_IMAGES: &str = "semantic-test-images";
pub const NATIVE_TEST_IMAGES: &str = "native-test-images";
pub const CLI_CHECK_IMAGES: &str = "cli-check-images";
pub const DECL_CACHE: &str = "decl-cache";

fn cache_dir_env() -> Option<PathBuf> {
    std::env::var_os(CACHE_DIR_ENV).filter(|d| !d.is_empty()).map(PathBuf::from)
}

/// Where the suites' and gates' stores live: `$HEATHER_CACHE_DIR`, else the
/// checkout's `target/`. Independent of `CARGO_TARGET_DIR`, which moves
/// Cargo's build and not these.
pub fn store_root(repo_root: &Path) -> PathBuf {
    match cache_dir_env() {
        Some(dir) => repo_root.join(dir),
        None => repo_root.join("target"),
    }
}

/// One named store beneath [`store_root`] ([`SEMANTIC_TEST_IMAGES`] and the rest).
pub fn shared_store(repo_root: &Path, name: &str) -> PathBuf {
    store_root(repo_root).join(name)
}

/// `heather check --cache`'s directory when no `--cache-dir` names one:
/// `$HEATHER_CACHE_DIR/check`, else [`DEFAULT_DIR`].
pub fn default_dir() -> PathBuf {
    match cache_dir_env() {
        Some(dir) => dir.join("check"),
        None => PathBuf::from(DEFAULT_DIR),
    }
}

/// What a run did, for the output line that keeps trust visible.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct Counts {
    /// Declarations the kernel actually gated.
    pub checked: usize,
    /// Declarations admitted on the cache's word alone.
    pub hits: usize,
    /// Full identity computations — the interface walk plus the check-key
    /// walk of one declaration. `admits` and `accepted` ask about the same
    /// declaration, so on a run that gates N declarations this is N, not 2N;
    /// it was 2N until 2026-09-17 (`issues/merkle-walk-cold-share.md`).
    pub hashed: usize,
    /// Body-less declarations whose statement image replay re-checked
    /// ([`KernelGate::admits_statement`] said no).
    pub statements_checked: usize,
    /// Body-less declarations whose statement a stored verdict vouched for.
    pub statement_hits: usize,
    /// Module replays a stored verdict about the whole replay vouched for
    /// ([`KernelGate::admits_replay`]): their declarations were neither
    /// checked nor asked about one by one.
    pub replay_hits: usize,
}

impl Counts {
    pub fn since(&self, earlier: &Counts) -> Counts {
        Counts {
            checked: self.checked - earlier.checked,
            hits: self.hits - earlier.hits,
            hashed: self.hashed - earlier.hashed,
            statements_checked: self.statements_checked - earlier.statements_checked,
            statement_hits: self.statement_hits - earlier.statement_hits,
            replay_hits: self.replay_hits - earlier.replay_hits,
        }
    }
}

/// The name a statement verdict is stored under. Names are metadata
/// (`docs/cache-v1-design.md` §8) and replay has none to give.
pub const STATEMENT_ENTRY: &str = "<statement>";
/// The name column of a whole-replay verdict ([`KernelGate::replay_accepted`]).
pub const REPLAY_ENTRY: &str = "<replay>";

struct Inner {
    store: Store,
    /// Interface hash per Ψ binding, in binding order. `None` is a poisoned
    /// binding (`merkle::Prefix`).
    prefix: Vec<Option<Hash>>,
    /// The interface hash computed for the item currently at the gate, and the
    /// index it will land at. Lets `sync` reuse it instead of re-rendering the
    /// binding a third time.
    pending: Option<(usize, Option<Hash>)>,
    /// The interface hash [`KernelGate::admits_statement`] computed, with the
    /// binding it describes and the index it was asked at. Image replay asks
    /// before it pushes the binding, so `sync` would otherwise render every
    /// replayed statement twice. Unlike `pending` it is used only when the
    /// binding that landed is that binding (`==`, which is pointer equality
    /// for a replayed binding's shared children): a replay that fails after
    /// asking lands something else at that index, and must not inherit it.
    statement: Option<(usize, heather_kernel::term::GlobalBinding, Option<Hash>)>,
    /// The Ψ whose first `prefix.len()` bindings `prefix` describes. An
    /// elaborator and its forks share one gate and ask about different Ψs
    /// in turn (`write-elf` reads its program on forks, then checks the
    /// certificate on the parent), so `sync` keeps only as much of `prefix`
    /// as the asking Ψ has in common with this one. `None` with an empty
    /// prefix.
    mark: Option<heather_kernel::term::GlobalMark>,
    /// The open questions: identities computed by [`Inner::identify`] for
    /// declarations `admits` has been asked about and `accepted` has not yet
    /// answered, keyed by the Ψ length they were asked at, then by name and
    /// opacity. Hashing a declaration is a full render of it — the one thing
    /// on this path that costs real time — and `accepted` asks the same
    /// question `admits` asked: immediately after, with the inline gate, or
    /// at the join of a deferred pass, when many other declarations have
    /// been asked about since and each is answered against the Ψ snapshot it
    /// was queued with. A single "last question" memo keyed on Ψ length
    /// served the first shape and missed the second on every item, so the
    /// deferred gate hashed everything twice and rebuilt the prefix once per
    /// module (`issues/merkle-walk-cold-share.md`).
    ///
    /// Exactness is what makes this safe to consult before hashing anything:
    /// an entry is opened by `admits`, closed by the `admits` hit or the
    /// `accepted` that answers it, and killed by [`KernelGate::abandon`] when
    /// its declaration fails — the elaborator keeps going after a refused
    /// declaration, and the next one lands at the same Ψ length. As a belt,
    /// a second Ψ-landing question at one length kills the first: only one
    /// declaration can be waiting to land at a position.
    open: BTreeMap<usize, Vec<OpenQuestion>>,
    counts: Counts,
}

struct OpenQuestion {
    name: String,
    opaque: bool,
    lands_in_psi: bool,
    answer: Option<(Hash, Hash)>,
}

/// The gate oracle. Install with `Elaborator::set_gate`; share one across
/// every root of a run so that a declaration checked for one file is not
/// re-checked for the next.
pub struct Cache {
    inner: RefCell<Inner>,
}

impl Cache {
    /// Open the cache at `dir`. Returns the cache and, when an existing file
    /// had to be thrown away, the reason — which the caller is expected to
    /// print (`store::Rejected::message`).
    pub fn open(dir: PathBuf) -> (Cache, Option<store::Rejected>) {
        let (store, why) = match Store::load(dir, KERNEL_SEMANTICS) {
            Ok(s) => (s, None),
            Err((s, r)) => (s, Some(r)),
        };
        (Cache::over(store), why)
    }

    /// A cache with no file behind it: for tests, and for a run that wants the
    /// hashing without the persistence.
    pub fn over(store: Store) -> Cache {
        Cache {
            inner: RefCell::new(Inner {
                store,
                prefix: Vec::new(),
                pending: None,
                statement: None,
                mark: None,
                open: BTreeMap::new(),
                counts: Counts::default(),
            }),
        }
    }

    pub fn counts(&self) -> Counts {
        self.inner.borrow().counts
    }

    pub fn entries(&self) -> usize {
        self.inner.borrow().store.entries.len()
    }

    /// Write the file back if anything was added.
    pub fn save(&self) -> std::io::Result<()> {
        let inner = self.inner.borrow();
        if inner.store.dirty {
            inner.store.save(KERNEL_SEMANTICS)?;
        }
        Ok(())
    }

    /// The interface hashes this cache has computed, in Ψ order. Test-facing:
    /// it is how the statement-vs-proof tests observe what moved.
    pub fn interface_hashes(&self) -> Vec<Option<Hash>> {
        self.inner.borrow().prefix.clone()
    }

    /// Every check key recorded, in sorted order. Test-facing, same reason.
    pub fn keys(&self) -> Vec<String> {
        self.inner.borrow().store.entries.keys().cloned().collect()
    }

    /// Recorded entries by name: `name → (check key, interface hash)`.
    ///
    /// Test-facing. Names are metadata and identity is the key
    /// (`docs/cache-v1-design.md` §8) — this exists so a test can ask "did
    /// *that* declaration's key move", which is how the red-green rule is
    /// observed at all.
    pub fn recorded(&self) -> std::collections::BTreeMap<String, (String, String)> {
        self.inner
            .borrow()
            .store
            .entries
            .iter()
            .map(|(k, e)| (e.name.clone(), (k.clone(), sha256::hex(&e.iface))))
            .collect()
    }

    /// Start a new elaboration against this cache.
    ///
    /// The prefix of interface hashes describes **one** Ψ, and each root file
    /// gets its own fresh elaborator with its own Ψ. Carrying the previous
    /// root's prefix into the next one would hash new declarations against
    /// referents they do not have. The stored entries survive — those are
    /// content-addressed and belong to no particular Ψ — which is the whole
    /// reason one cache is shared across roots.
    pub fn begin_run(&self) {
        let mut inner = self.inner.borrow_mut();
        inner.prefix.clear();
        inner.pending = None;
        inner.statement = None;
        inner.mark = None;
        inner.open.clear();
    }
}

impl Inner {
    /// Bring `prefix` up to Ψ's length.
    ///
    /// Bindings normally arrive one at a time through the gate, but not all of
    /// them do — the prelude is elaborated before any gate can be installed —
    /// so this absorbs whatever it finds rather than assuming. That is also
    /// what makes the cache's view of Ψ correct for a caller that pushes
    /// bindings of its own.
    fn sync(&mut self, psi: &GlobalCtx) {
        // Keep the hashes of the bindings this Ψ shares with the one the
        // prefix was built along, and only those: hashing against a stale
        // prefix would produce keys that mean nothing. Until 2026-10-29 a
        // shorter Ψ cleared the prefix and a longer one was trusted unread,
        // so each switch between an elaborator and its forks re-hashed the
        // whole world (seconds per `write-elf`, on its first probe
        // declaration and its certificate,
        // `issues/native-process-fixed-cost.md`), and a fork that had grown
        // past a sibling's bindings without asking would have hashed against
        // the sibling's.
        let common = match &self.mark {
            Some(mark) => psi.bindings.common_prefix(mark).min(self.prefix.len()),
            None => 0,
        };
        if common < self.prefix.len() {
            self.prefix.truncate(common);
            self.pending = None;
            self.statement = None;
            // A question asked past the common part was asked about another
            // Ψ's declaration.
            self.open.split_off(&(common + 1));
        }
        while self.prefix.len() < psi.bindings.len() {
            let i = self.prefix.len();
            let h = match (self.pending.take(), self.statement.take()) {
                (Some((idx, h)), _) if idx == i => h,
                (_, Some((idx, b, h))) if idx == i && b == psi.bindings[i] => h,
                _ => merkle::interface_hash(&self.prefix, &psi.bindings[i]),
            };
            self.prefix.push(h);
        }
        self.pending = None;
        self.statement = None;
        self.mark = Some(psi.bindings.mark());
    }

    /// The statement key of `binding` about to land at `psi.bindings.len()`,
    /// remembering its interface hash for `sync`. `None` when unhashable.
    fn statement_key(&mut self, psi: &GlobalCtx, binding: &heather_kernel::term::GlobalBinding) -> Option<(Hash, Hash)> {
        self.sync(psi);
        let at = self.prefix.len();
        let iface = match &self.statement {
            Some((idx, b, h)) if *idx == at && b == binding => *h,
            _ => {
                let h = merkle::interface_hash(&self.prefix, binding);
                self.statement = Some((at, binding.clone(), h));
                h
            }
        };
        let iface = iface?;
        Some((iface, merkle::statement_key(&self.prefix, &iface)?))
    }

    /// Interface hash and check key for the item at the gate, or `None` if
    /// either is unhashable (§3.1: fail closed, never cache).
    fn identify(&mut self, psi: &GlobalCtx, item: &GateItem<'_>) -> Option<(Hash, Hash)> {
        let at = psi.bindings.len();
        // The `admits`/`accepted` pair asks about one declaration in one Ψ;
        // answering twice would double the run's hashing, which is the whole
        // of its overhead. An open question is answered without touching the
        // prefix: at a deferred join, `psi` is the snapshot the declaration
        // was queued with and the prefix has long since grown past it.
        if let Some(q) = self.open.get(&at).and_then(|qs| {
            qs.iter().find(|q| q.opaque == item.opaque && q.name == item.name)
        }) {
            return q.answer;
        }
        // A miss. Questions open at a greater length were asked by a pass
        // that is not coming back (the join answers in order, and answers
        // never miss); a Ψ-landing question open at *this* length is a
        // declaration that never landed.
        self.open.split_off(&(at + 1));
        if let Some(qs) = self.open.get_mut(&at) {
            if item.lands_in_psi {
                qs.retain(|q| !q.lands_in_psi);
            }
        }
        self.sync(psi);
        self.counts.hashed += 1;
        // Hashing a declaration is a full render of it — the one thing on this
        // path that costs real time, and until now the only thing about it the
        // cache reported was a count (`docs/instrumentation-design.md` §5).
        heather_elab::stats::count(heather_elab::stats::Counter::CacheHashes);
        let _phase = heather_elab::stats::guard(heather_elab::stats::Timer::CacheHash);
        let binding = item.binding();
        if std::env::var_os("HEATHER_MERKLE_SHARE").is_some() {
            eprintln!("merkle-item\t{}\t{}\t{}", item.name, self.prefix.len(), item.opaque);
        }
        let iface = merkle::interface_hash(&self.prefix, &binding);
        // Recorded for `sync` whether or not it succeeded: the binding lands
        // at this index either way, and a poisoned entry must be *stored* as
        // poison so that its dependents fail closed too. Only for an item
        // that *does* land — a `meta fn` never reaches Ψ, and a pending hash
        // left behind for it would be absorbed by whatever binding lands at
        // this index next, mis-describing it to every dependent.
        if item.lands_in_psi {
            self.pending = Some((self.prefix.len(), iface));
        }
        let answer = (|| {
            let iface = iface?;
            let key = merkle::check_key(&self.prefix, item.body, item.opaque, &iface)?;
            // A check made under an interface boundary is a different
            // question: the same item may pass transparently and be refused
            // with bodies withheld (docs/interface-definitions-design.md §3).
            let key = match psi.withheld.as_deref() {
                Some(withheld) => {
                    let mut h = crate::sha256::Sha256::new();
                    h.update(b"heather-withheld-check\0");
                    h.update(&key);
                    for (at, arity) in withheld.entries() {
                        h.update(&(at as u64).to_le_bytes());
                        h.update(&arity.to_le_bytes());
                    }
                    h.finish()
                }
                None => key,
            };
            Some((iface, key))
        })();
        self.open.entry(at).or_default().push(OpenQuestion {
            name: item.name.to_string(),
            opaque: item.opaque,
            lands_in_psi: item.lands_in_psi,
            answer,
        });
        answer
    }

    /// Close a question: it has been answered (an `admits` hit, or the
    /// `accepted` that follows a miss), so nothing will ask it again.
    fn close(&mut self, psi: &GlobalCtx, item: &GateItem<'_>) {
        let at = psi.bindings.len();
        if let Some(qs) = self.open.get_mut(&at) {
            qs.retain(|q| !(q.opaque == item.opaque && q.name == item.name));
            if qs.is_empty() {
                self.open.remove(&at);
            }
        }
    }
}

impl KernelGate for Cache {
    fn admits(&self, psi: &GlobalCtx, item: &GateItem<'_>) -> bool {
        let mut inner = self.inner.borrow_mut();
        let Some((_, key)) = inner.identify(psi, item) else {
            inner.counts.checked += 1;
            return false;
        };
        if inner.store.contains(&key) {
            inner.counts.hits += 1;
            // A hit ends the question: no `accepted` follows.
            inner.close(psi, item);
            true
        } else {
            inner.counts.checked += 1;
            false
        }
    }

    fn accepted(&self, psi: &GlobalCtx, item: &GateItem<'_>, unsealed: &[usize]) {
        let mut inner = self.inner.borrow_mut();
        // A check that opened a sealed proof leaned on that proof's body,
        // which no interface hash covers: its verdict is not stored, so a
        // later run re-checks it against whatever the proof is then
        // (`issues/theorem-witness-unfolding.md`). A check that opened none
        // took the same path whatever the sealed proofs are — which theorems
        // carry one is fixed by their statements — so its key stays sound.
        if unsealed.is_empty() {
            if let Some((iface, key)) = inner.identify(psi, item) {
                inner.store.insert(key, iface, item.name);
            }
        } else {
            // `identify` still runs: the binding's interface hash is pending
            // for `sync` whether or not a verdict is kept.
            inner.identify(psi, item);
        }
        inner.close(psi, item);
    }

    fn abandon(&self, psi: &GlobalCtx) {
        self.inner.borrow_mut().open.split_off(&psi.bindings.len());
    }

    /// A statement verdict is "the kernel accepted this binding's statement
    /// in a context whose interfaces hash thus": the interface hash covers
    /// the statement and, through its references, everything the statement
    /// check reads (`merkle::statement_key`).
    /// A whole module replay, keyed by its caller (the bytes and the world
    /// under them, `docs/module-dag-design.md` §13). Its interface hashes are
    /// not taken: the prefix absorbs them lazily if a later declaration asks.
    fn admits_replay(&self, key: &[u8; 32]) -> bool {
        let mut inner = self.inner.borrow_mut();
        let hit = inner.store.contains(key);
        if hit {
            inner.counts.replay_hits += 1;
        }
        hit
    }

    fn replay_accepted(&self, key: &[u8; 32]) {
        self.inner.borrow_mut().store.insert(*key, *key, REPLAY_ENTRY);
    }

    fn admits_statement(&self, psi: &GlobalCtx, binding: &heather_kernel::term::GlobalBinding) -> bool {
        let mut inner = self.inner.borrow_mut();
        let hit = match inner.statement_key(psi, binding) {
            Some((_, key)) => inner.store.contains(&key),
            None => false,
        };
        if hit {
            inner.counts.statement_hits += 1;
        } else {
            inner.counts.statements_checked += 1;
        }
        hit
    }

    fn statement_accepted(&self, psi: &GlobalCtx, binding: &heather_kernel::term::GlobalBinding, unsealed: &[usize]) {
        // The same rule as `accepted`: a check that opened a sealed proof
        // leaned on a body no interface hash covers.
        if !unsealed.is_empty() {
            return;
        }
        let mut inner = self.inner.borrow_mut();
        if let Some((iface, key)) = inner.statement_key(psi, binding) {
            inner.store.insert(key, iface, STATEMENT_ENTRY);
        }
    }

    fn assumption(
        &self,
        psi: &GlobalCtx,
        _name: &str,
        binding: &heather_kernel::term::GlobalBinding,
    ) {
        let mut inner = self.inner.borrow_mut();
        inner.sync(psi);
        let at = inner.prefix.len();
        let hash = merkle::assumption_interface_hash(&inner.prefix, binding);
        inner.pending = Some((at, hash));
        inner.counts.checked += 1;
    }
}
