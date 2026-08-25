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
use std::path::PathBuf;

use heather_elab::gate::{GateItem, KernelGate};
use heather_kernel::term::GlobalCtx;

pub mod merkle;
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

/// The per-repository cache directory, relative to the working directory.
pub const DEFAULT_DIR: &str = ".heather/cache";

/// What a run did, for the output line that keeps trust visible.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct Counts {
    /// Declarations the kernel actually gated.
    pub checked: usize,
    /// Declarations admitted on the cache's word alone.
    pub hits: usize,
}

impl Counts {
    pub fn since(&self, earlier: &Counts) -> Counts {
        Counts { checked: self.checked - earlier.checked, hits: self.hits - earlier.hits }
    }
}

struct Inner {
    store: Store,
    /// Interface hash per Ψ binding, in binding order. `None` is a poisoned
    /// binding (`merkle::Prefix`).
    prefix: Vec<Option<Hash>>,
    /// The interface hash computed for the item currently at the gate, and the
    /// index it will land at. Lets `sync` reuse it instead of re-rendering the
    /// binding a third time.
    pending: Option<(usize, Option<Hash>)>,
    /// The identity computed by the most recent [`Inner::identify`], with the
    /// Ψ length it was computed at. `accepted` follows `admits` immediately
    /// and asks the same question, and hashing a declaration is a full render
    /// of it — the one thing on this path that costs real time.
    last: Option<(usize, Hash, Hash)>,
    counts: Counts,
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
                last: None,
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
        inner.last = None;
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
        // Belt to `Cache::begin_run`'s braces: a Ψ shorter than the prefix is
        // certainly a different Ψ, and hashing against a stale prefix would
        // produce keys that mean nothing. Cheap, and it fails towards
        // recomputation rather than towards a wrong key.
        if self.prefix.len() > psi.bindings.len() {
            self.prefix.clear();
            self.pending = None;
            self.last = None;
        }
        while self.prefix.len() < psi.bindings.len() {
            let i = self.prefix.len();
            let h = match self.pending.take() {
                Some((idx, h)) if idx == i => h,
                _ => merkle::interface_hash(&self.prefix, &psi.bindings[i]),
            };
            self.prefix.push(h);
        }
        self.pending = None;
    }

    /// Interface hash and check key for the item at the gate, or `None` if
    /// either is unhashable (§3.1: fail closed, never cache).
    fn identify(&mut self, psi: &GlobalCtx, item: &GateItem<'_>) -> Option<(Hash, Hash)> {
        self.sync(psi);
        // The `admits`/`accepted` pair asks about one declaration in one Ψ;
        // answering twice would double the run's hashing, which is the whole
        // of its overhead. Keyed on the Ψ length so a mismatched pair
        // recomputes rather than answers about the wrong thing. (Sound for a
        // non-Ψ item too — two of those could share a Ψ length, so `admits`/
        // `accepted` clear this memo the moment such an item is answered.)
        if let Some((at, iface, key)) = self.last
            && at == psi.bindings.len()
        {
            return Some((iface, key));
        }
        let binding = item.binding();
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
        let iface = iface?;
        let key = merkle::check_key(&self.prefix, item.body, item.opaque, &iface)?;
        self.last = Some((psi.bindings.len(), iface, key));
        Some((iface, key))
    }

    /// Forget the `admits`/`accepted` memo. Called once a non-Ψ item's
    /// question is fully answered: its Ψ length is not unique to it, so a
    /// later item at the same length must never inherit its hashes.
    fn forget(&mut self) {
        self.last = None;
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
            // A hit ends the question: no `accepted` follows, so a non-Ψ
            // item's memo must die here rather than answer for the next item
            // at this Ψ length.
            if !item.lands_in_psi {
                inner.forget();
            }
            true
        } else {
            inner.counts.checked += 1;
            false
        }
    }

    fn accepted(&self, psi: &GlobalCtx, item: &GateItem<'_>) {
        let mut inner = self.inner.borrow_mut();
        if let Some((iface, key)) = inner.identify(psi, item) {
            inner.store.insert(key, iface, item.name);
        }
        // Same reason as the hit path in `admits`: the pair is answered.
        if !item.lands_in_psi {
            inner.forget();
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
        inner.last = None;
    }
}
