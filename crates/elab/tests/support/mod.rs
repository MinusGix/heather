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
