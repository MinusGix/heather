//! Shared fixtures for the integration tests.
//!
//! Included by `mod support;` in more than one test target, and each target
//! uses a different part of it, so unused-item warnings here are expected.
//!
//! Orientation, so nobody greps for these twice (finding the prelude took a
//! four-call hunt in one session, 2026-08-11):
//!
//! - **The test prelude** is `crates/elab/src/prelude.hthr` (`PRELUDE` in
//!   `lib.rs` includes it; `Elaborator::with_prelude` elaborates it). It is
//!   what defines `add`, `List`, `sym`/`trans`/`cong` and friends for every
//!   snippet test — there is no `prelude.hthr` under `lib/`.
//! - **Harness helpers** (`ok`/`bad`/`bare`, and per-file variants) are
//!   local `fn`s at the top of each test file, not shared here — each file
//!   pins its own prelude-plus-fixture combination on purpose.
//! - **The whole-library acceptance tests** (`lib/std`, `lib/ir_v1.hthr`)
//!   live in `lib_algebra.rs` / `lib_list_algos.rs` / `ir_v1.rs` /
//!   `certgen.rs`; the two expensive ones — the `--fast` skips named in
//!   `scripts/test` — are in `ir_v1.rs` and `certgen.rs`.
//! - **What a generated-term test must vary**: docs/testing-generated-terms.md.
#![allow(dead_code)]

use std::rc::Rc;

use heather_kernel::term::GlobalCtx;

/// The Nat arithmetic + Id lemma suite: stress-proof-suite item 1, and the
/// corpus the determinism/golden-hash tests elaborate. Lives here rather
/// than in `nat_suite.rs` so that both targets pin the *same* source — a
/// golden hash of a private copy would drift silently from the suite it
/// claims to describe.
///
/// These are the **stage-1 explicit forms**: `as λ z => M` motives spelled
/// out, and endpoints to the (now implicit-parametered) prelude lemmas
/// supplied positionally via `@` (issues/elab-stage2-metas.md). The
/// annotation-free stage-2 forms live in `implicit_args.rs`.
pub const NAT_SUITE: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n as λ z => add(z, 0) = z {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, 0), k, ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m as λ z => add(z, Succ(n)) = Succ(add(z, n)) {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, Succ(n)), Succ(add(k, n)), ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m as λ z => add(z, n) = add(n, z) {
        Zero => @sym(add(n, 0), n, add_zero(n)),
        Succ(k, ih) => @trans(
            Succ(add(k, n)),
            Succ(add(n, k)),
            add(n, Succ(k)),
            @cong_succ(add(k, n), add(n, k), ih),
            @sym(add(n, Succ(k)), Succ(add(n, k)), add_succ(n, k))
        ),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a as λ z => add(add(z, b), c) = add(z, add(b, c)) {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(add(k, b), c), add(k, add(b, c)), ih),
    }
}
"#;

/// The certgen family's shared declaration cache
/// (`issues/elaborator-snapshot-across-test-binaries.md`).
///
/// Five certgen test binaries each elaborate the same checked-in prefix —
/// `lib/ir_v1.hthr`'s declarations (or the support-prelude slice of it),
/// `lib/certgen_code.hthr`, `lib/certgen_cert.hthr` — before their own
/// content starts: identical work, re-kernel-checked once per binary. The CLI
/// already owns the mechanism that makes paying it once sound — the
/// content-addressed declaration cache behind `heather check --cache`
/// (docs/cache-v1-design.md) — and the elaborator already exposes the seam it
/// installs through (`Elaborator::set_gate`). This helper wires the tests to
/// the same store shape, at `target/decl-cache`.
///
/// The trust argument is the cache's own (design doc §6): an entry is
/// recorded only when *this* kernel — the `KERNEL_SEMANTICS` fingerprint,
/// computed by the cache crate's build script over `crates/kernel/src` —
/// accepted exactly this elaborated content against exactly these referents'
/// interface hashes. A changed library file, prelude or elaboration output
/// changes every downstream key (a miss, a full check); a changed kernel
/// discards the whole store, loudly, on open. `DEFAULT_FUEL` is a
/// `crates/kernel/src` constant, so the fuel caveat of
/// `issues/cache-verdicts-omit-check-settings.md` is covered by the
/// fingerprint for as long as fuel stays one.
///
/// Two rules keep the suite meaning what it meant:
///
/// - **The gate never covers generated or mutated content.** Callers wrap
///   exactly the checked-in prefix elaborations; on return the gate is
///   `NoGate` again, so every generated emission, fixture `fn` and
///   perturbed-library mutant is kernel-checked in full on every run
///   (docs/testing-generated-terms.md keeps its teeth).
/// - **One binary takes no gate at all**: `certgen_emissions.rs` elaborates
///   the whole prefix front-to-back against the real kernel every full-suite
///   run, as the backstop against a defect in the cache mechanism itself.
///
/// Cold path: nothing to pre-run — a fresh checkout (or `cargo clean`)
/// simply records on first use and reuses after. Concurrent tests race the
/// final save (atomic via rename, last writer wins); a lost update costs a
/// re-check on the next run, never a wrong answer.
pub fn with_decl_cache(e: &mut heather_elab::Elaborator, prefix: impl FnOnce(&mut heather_elab::Elaborator)) {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/decl-cache");
    let (cache, rejected) = heather_cache::Cache::open(dir.clone());
    // A discarded store says why (a changed kernel, a corrupt file): the one
    // thing a cache must never do is quietly do nothing.
    if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) {
        eprintln!("decl-cache: {msg}");
    }
    let cache = Rc::new(cache);
    e.set_gate(Rc::clone(&cache) as Rc<dyn heather_elab::gate::KernelGate>);
    prefix(e);
    // Seal: from here on the kernel sees everything again.
    e.set_gate(Rc::new(heather_elab::gate::NoGate));
    let n = cache.counts();
    eprintln!(
        "decl-cache: {} declaration{} kernel-checked, {} accepted from cache",
        n.checked,
        if n.checked == 1 { "" } else { "s" },
        n.hits
    );
    if let Err(err) = cache.save() {
        eprintln!("decl-cache: could not write {}: {err}", dir.display());
    }
}

/// A 64-bit FNV-1a over an exact rendering of Ψ.
///
/// First-party on purpose: `crates/elab` has no dependencies, dev-deps
/// included (issues/dependency-policy.md), so a snapshot library is not
/// available and a `Hash` derive on the kernel types does not exist (and
/// `DefaultHasher` is explicitly not stable across releases). FNV-1a is ten
/// lines and stable by definition, which is all a golden value needs.
///
/// The rendering is [`heather_kernel::fmt::write_exact`], *not* `{:?}`: the
/// ordinary kernel `Debug` elides past 512 nodes, so two Ψs agreeing on a
/// prefix would hash alike — the exact opposite of what a golden hash is for.
/// It streams into the hasher, so nothing the size of the printed tree is
/// ever held in memory.
pub fn psi_hash(psi: &GlobalCtx) -> u64 {
    let mut h = Fnv1a::new();
    heather_kernel::fmt::write_exact(&mut h, psi).expect("Fnv1a never fails to write");
    h.0
}

pub struct Fnv1a(pub u64);

impl Fnv1a {
    pub fn new() -> Fnv1a {
        Fnv1a(0xcbf2_9ce4_8422_2325)
    }

    pub fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 ^= u64::from(*b);
            self.0 = self.0.wrapping_mul(0x100_0000_01b3);
        }
    }
}

impl Default for Fnv1a {
    fn default() -> Fnv1a {
        Fnv1a::new()
    }
}

/// So the hasher can *be* the format sink: `write_exact` streams UTF-8
/// fragments straight in, with no intermediate `String`.
impl std::fmt::Write for Fnv1a {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.write(s.as_bytes());
        Ok(())
    }
}
