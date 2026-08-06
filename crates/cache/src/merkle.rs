//! Content addressing: the hash of an elaborated declaration with every
//! global reference replaced by the hash of its referent's interface
//! (`docs/cache-v1-design.md` §3 and §5, `issues/parallel-checking-and-caching.md`).
//!
//! The rendering is `heather_kernel::fmt::write_exact` — the kernel's own
//! `Debug` with the node/depth elision disarmed, streaming, total,
//! deterministic. Reusing it means the cache's notion of "same term" *is* the
//! notion `issues/elaboration-determinism.md`'s golden hash guards, rather
//! than a second implementation that has to be kept in agreement with it.
//!
//! The substitution happens in the sink, as a state machine over the
//! character stream. Its correctness rests on one assumption about the
//! kernel's printed form, stated here and pinned by `tests/merkle.rs`:
//!
//! > A global reference prints as `u<digits>` (a term, `Term::GlobalTm`),
//! > `U<digits>` (a type, `Type::GlobalTy`) or `g<digits>` (a context-variable
//! > base, `CtxBase::Var`), and nothing else in `crates/kernel/src/fmt.rs`
//! > emits an ASCII-alphanumeric-free `u`/`U`/`g` followed by digits.
//!
//! Verified by reading every format string in that file on 2026-08-06. If a
//! kernel change breaks it, `rewrites_every_global_spelling` and
//! `the_same_declaration_at_two_positions_agrees` fail — which is what makes
//! the assumption maintainable rather than merely stated.

use std::fmt::Write;

use heather_kernel::layer::Layer;
use heather_kernel::term::{GlobalBinding, Term};

use crate::sha256::{Sha256, hex};

/// A 32-byte content hash.
pub type Hash = [u8; 32];

/// Domain separation. The two hash families must never be confusable: an
/// interface hash answers "what do dependents see", a check key answers "did
/// the kernel accept this", and they are computed over overlapping material.
const DOMAIN_IFACE: &str = "heather/iface/1\0";
const DOMAIN_CHECK: &str = "heather/check/1\0";

/// The interface hashes of a Ψ prefix, in binding order.
///
/// `None` at an index is a **poisoned** binding: one whose own hash could not
/// be computed (§3.1's fail-closed path). Anything referencing it is not
/// hashable either, so the poison propagates and the declaration is simply
/// never cached — a missing key can only cost time.
pub type Prefix = [Option<Hash>];

/// A `fmt::Write` sink that rewrites global references into referent hashes on
/// the way through to `out`.
struct Rewriter<'a, W: Write> {
    out: W,
    prefix: &'a Prefix,
    /// The length of Ψ that the term being rendered is scoped over. A
    /// reference `u k` denotes absolute index `len − 1 − k`.
    len: u32,
    state: State,
    /// Was the previous *source* character ASCII-alphanumeric? A marker
    /// letter only starts a reference when it does not continue a word — this
    /// is what keeps the `u` of `sup` from being read as a global.
    prev_alnum: bool,
    /// Set when a reference resolved outside the prefix or hit poison. Once
    /// set, the result is discarded: no key is produced at all.
    poisoned: bool,
}

#[derive(Clone, Copy)]
enum State {
    Idle,
    /// Seen a marker letter; whether it is a reference depends on the next
    /// character.
    Marker(char),
    /// Collecting the digits of a reference.
    Digits(char, u32),
}

impl<'a, W: Write> Rewriter<'a, W> {
    fn new(out: W, prefix: &'a Prefix, len: u32) -> Rewriter<'a, W> {
        Rewriter { out, prefix, len, state: State::Idle, prev_alnum: false, poisoned: false }
    }

    fn put(&mut self, c: char) {
        let _ = self.out.write_char(c);
    }

    fn put_str(&mut self, s: &str) {
        if !s.is_empty() {
            let _ = self.out.write_str(s);
        }
    }

    /// Emit the referent's interface hash in place of the positional index.
    /// The marker letter is kept, so a term, a type and a context reference to
    /// one binding stay distinguishable.
    fn put_ref(&mut self, marker: char, var: u32) {
        self.put(marker);
        match self
            .len
            .checked_sub(1)
            .and_then(|l| l.checked_sub(var))
            .and_then(|abs| self.prefix.get(abs as usize).copied().flatten())
        {
            Some(h) => {
                let mut buf = [0u8; 64];
                crate::sha256::hex_into(&h, &mut buf);
                let _ = self.out.write_str(std::str::from_utf8(&buf).expect("ASCII"));
            }
            None => self.poisoned = true,
        }
    }

    /// Scan one fragment, passing the (overwhelmingly common) uninteresting
    /// stretches through as whole slices.
    ///
    /// Character-at-a-time would be far simpler and was measurably too slow:
    /// on `lib/ir_v1.hthr` the printed tree runs to tens of megabytes and a
    /// per-character `Sha256::update` spends all its time in the partial-block
    /// bookkeeping. `run` is the start of the pass-through stretch in flight;
    /// it is closed only when a marker letter actually appears.
    fn scan(&mut self, s: &str) {
        let mut run: Option<usize> = None;
        for (i, c) in s.char_indices() {
            match self.state {
                State::Idle => {
                    if matches!(c, 'u' | 'U' | 'g') && !self.prev_alnum {
                        if let Some(r) = run.take() {
                            self.put_str(&s[r..i]);
                        }
                        self.state = State::Marker(c);
                    } else if run.is_none() {
                        run = Some(i);
                    }
                }
                State::Marker(m) => match c.to_digit(10) {
                    Some(d) => self.state = State::Digits(m, d),
                    None => {
                        // Not a reference after all: the marker was an
                        // ordinary letter. Emit it, then let `c` start a new
                        // run — it cannot itself be a marker, since the letter
                        // before it is alphanumeric.
                        self.put(m);
                        self.state = State::Idle;
                        run = Some(i);
                    }
                },
                State::Digits(m, n) => match c.to_digit(10) {
                    // Saturating rather than wrapping: an absurd index must
                    // stay absurd, and it will then fail to resolve.
                    Some(d) => {
                        self.state = State::Digits(m, n.saturating_mul(10).saturating_add(d))
                    }
                    None => {
                        self.put_ref(m, n);
                        self.state = State::Idle;
                        run = Some(i);
                    }
                },
            }
            self.prev_alnum = c.is_ascii_alphanumeric();
        }
        if let Some(r) = run {
            self.put_str(&s[r..]);
        }
    }

    /// Drain the state machine and hand back the sink, or `None` if any
    /// reference failed to resolve.
    fn done(mut self) -> Option<W> {
        match self.state {
            State::Idle => {}
            State::Marker(m) => self.put(m),
            State::Digits(m, n) => self.put_ref(m, n),
        }
        if self.poisoned { None } else { Some(self.out) }
    }
}

impl<W: Write> Write for Rewriter<'_, W> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.scan(s);
        Ok(())
    }
}

/// `write_exact` into `sink`. The sinks here never fail.
fn exact<W: Write>(sink: &mut Rewriter<'_, W>, value: &impl std::fmt::Debug) {
    heather_kernel::fmt::write_exact(sink, value).expect("these sinks never fail to write");
}

fn layer_tag(l: Layer) -> &'static str {
    match l {
        Layer::Var => "v",
        Layer::Code => "c",
        Layer::Prog => "p",
        Layer::Meta => "m",
    }
}

/// Render one binding as its **interface** — which is simply the binding as Ψ
/// stores it, because Ψ already implements the interface split: a `theorem` is
/// pushed with `body: None`, a `fn` with its body (`docs/cache-v1-design.md`
/// §4). Written out field by field rather than through the derived `Debug` so
/// that the framing is this module's, not a derive's.
fn write_binding<W: Write>(sink: &mut Rewriter<'_, W>, b: &GlobalBinding) {
    match b {
        GlobalBinding::Ctx => {
            let _ = sink.write_str("B:ctx");
        }
        GlobalBinding::Ty { ctx, layer, level } => {
            let _ = sink.write_str("B:ty|");
            exact(sink, ctx);
            let _ = sink.write_str("|");
            let _ = sink.write_str(layer_tag(*layer));
            let _ = sink.write_str("|");
            exact(sink, level);
        }
        GlobalBinding::Tm { ctx, layer, ty, level, body } => {
            let _ = sink.write_str("B:tm|");
            exact(sink, ctx);
            let _ = sink.write_str("|");
            let _ = sink.write_str(layer_tag(*layer));
            let _ = sink.write_str("|");
            exact(sink, &**ty);
            let _ = sink.write_str("|");
            exact(sink, level);
            match body {
                // Opaque-vs-transparent is part of the interface: a `fn`'s
                // body is δ-visible downstream, a `theorem`'s is not.
                None => {
                    let _ = sink.write_str("|opaque");
                }
                Some(t) => {
                    let _ = sink.write_str("|def:");
                    exact(sink, &**t);
                }
            }
        }
    }
}

fn hasher<'a>(domain: &str, prefix: &'a Prefix, len: u32) -> Rewriter<'a, Sha256> {
    let mut h = Sha256::new();
    h.update(domain.as_bytes());
    Rewriter::new(h, prefix, len)
}

/// The interface hash of the binding that will sit at absolute index
/// `prefix.len()`, given the interface hashes of everything before it.
///
/// `None` means "not hashable" — a reference this module could not resolve —
/// and every caller treats that as "do not cache", never as an error.
pub fn interface_hash(prefix: &Prefix, b: &GlobalBinding) -> Option<Hash> {
    let mut sink = hasher(DOMAIN_IFACE, prefix, prefix.len() as u32);
    write_binding(&mut sink, b);
    Some(sink.done()?.finish())
}

/// The cache identity of one kernel gate: "the kernel accepted *this* proof of
/// *this* interface, in a context whose interfaces hash thus".
///
/// The proof term is here and not in a theorem's interface hash, which is the
/// whole of the red-green rule (`docs/cache-v1-design.md` §5): editing a proof
/// moves this and nothing else; editing a statement moves this *and* the
/// interface, hence every dependent's key.
///
/// A **transparent** declaration needs nothing beyond its interface hash: a
/// `fn`'s body is already in there, because it is δ-visible downstream. So
/// only a theorem pays a second rendering, and the total rendering cost of a
/// declaration is its own content exactly once — which matters, since this
/// runs on the warm path where the kernel does not.
pub fn check_key(prefix: &Prefix, body: &Term, opaque: bool, iface: &Hash) -> Option<Hash> {
    let mut sink = hasher(DOMAIN_CHECK, prefix, prefix.len() as u32);
    let _ = sink.write_str(&hex(iface));
    if !opaque {
        let _ = sink.write_str("|def");
        return Some(sink.done()?.finish());
    }
    let _ = sink.write_str("|proof:");
    exact(&mut sink, body);
    Some(sink.done()?.finish())
}

/// The rewritten rendering as text rather than as a hash — the same state
/// machine over the same stream, differing only in the sink.
///
/// Exists for the canaries of `tests/merkle.rs`, which have to be able to say
/// *what* survived the rewrite and not merely that two hashes differ. The
/// shipped path never materializes a rendering.
#[doc(hidden)]
pub fn rewritten_text(prefix: &Prefix, len: u32, value: &impl std::fmt::Debug) -> Option<String> {
    let mut sink = Rewriter::new(String::new(), prefix, len);
    heather_kernel::fmt::write_exact(&mut sink, value).ok()?;
    sink.done()
}
