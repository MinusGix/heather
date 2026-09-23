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

pub mod parser;

use std::sync::Arc as Rc;

use heather_kernel::term::GlobalCtx;

/// Build an in-process test base from checked semantic module images.
///
/// The ordered input is the same dependency-first closure an ordinary test
/// used to elaborate by hand. A cold run checks every source module and
/// publishes beneath `target/semantic-test-images`; a warm run bounded-decodes
/// every stored suffix and, before metadata becomes visible, either has the
/// declaration-verdict store at `target/decl-cache` vouch for each stored
/// definition or kernel-checks it (stored theorems are statement-checked;
/// they carry no proof). The returned elaborator has `NoGate`, so fixture
/// theorems, mutations and controls always reach the real kernel.
pub fn semantic_test_base(modules: &[(&str, &str)]) -> heather_elab::Elaborator {
    semantic_test_base_with(modules, |_| {})
}

/// [`semantic_test_base`] with the elaborator configured *before* the prefix
/// is checked or replayed — for a target whose prefix carries a large checked
/// artifact and pins the gate serial to stay inside the per-process memory
/// rail on a cold run (the showcase calculator's grammar). Setting the width
/// on the returned elaborator would be too late for the cold path.
pub fn semantic_test_base_with(
    modules: &[(&str, &str)],
    configure: impl FnOnce(&mut heather_elab::Elaborator),
) -> heather_elab::Elaborator {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/semantic-test-images");
    semantic_test_base_in(modules, dir, configure)
}

/// The isolated-directory form used by the support boundary's own corruption
/// and rebuild controls. Ordinary suites should use [`semantic_test_base`]
/// so they share one content-addressed store beneath `target/`.
pub fn semantic_test_base_at(
    modules: &[(&str, &str)],
    dir: std::path::PathBuf,
) -> heather_elab::Elaborator {
    semantic_test_base_in(modules, dir, |_| {})
}

fn semantic_test_base_in(
    modules: &[(&str, &str)],
    dir: std::path::PathBuf,
    configure: impl FnOnce(&mut heather_elab::Elaborator),
) -> heather_elab::Elaborator {
    // `HEATHER_SEMANTIC_IMAGES=accept-stale` (the fast lane, set by
    // scripts/test) replays images an earlier build of the compiler wrote
    // instead of rebuilding every prefix after each Rust edit. A replayed
    // binding is vouched for by the verdict store or kernel-checked; what
    // the fast lane gives up is exercising the *current* frontend on
    // unchanged library modules, which the full lane's exact policy restores.
    let freshness = match std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() {
        Ok("accept-stale") => heather_cache::module_image::ImageFreshness::AcceptStale,
        _ => heather_cache::module_image::ImageFreshness::Exact,
    };
    let mut session = heather_cli::semantic::SemanticSession::new(Some(dir)).with_freshness(freshness);
    let mut elab = heather_elab::Elaborator::with_prelude().expect("prelude");
    configure(&mut elab);
    // The checked-in prefix goes through the declaration-verdict store as
    // well (`with_decl_cache`'s trust argument, below): a replayed image's
    // stored definitions ask the store the question the cold gate answered
    // (`docs/parallel-kernel-gate-design.md` §5.3), so a binary that replays
    // an unchanged prefix no longer rechecks every body per process. The
    // gate is sealed to `NoGate` before the caller's own content, as ever.
    let decl_cache = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/decl-cache");
    let (cache, rejected) = heather_cache::Cache::open(decl_cache.clone());
    if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) {
        eprintln!("decl-cache: {msg}");
    }
    let cache = Rc::new(cache);
    elab.set_gate(Rc::clone(&cache) as Rc<dyn heather_elab::gate::KernelGate>);
    for &(name, src) in modules {
        let module = heather_cli::loader::Module {
            name: name.into(),
            path: std::path::PathBuf::from(format!("{name}.hthr")),
            src: src.into(),
        };
        let outcome = session.check(
            &mut elab,
            &module,
            heather_elab::LintProfile::Default,
        );
        for notice in &outcome.notices {
            eprintln!("semantic-test-images: {notice}");
        }
        if !outcome.errors.is_empty() {
            let rendered = outcome
                .errors
                .iter()
                .map(|error| error.render(src))
                .collect::<Vec<_>>()
                .join("\n\n");
            panic!("{name} did not check:\n{rendered}");
        }
    }
    elab.set_gate(Rc::new(heather_elab::gate::NoGate));
    if let Err(err) = cache.save() {
        eprintln!("decl-cache: could not write {}: {err}", decl_cache.display());
    }
    if std::env::var_os("HEATHER_SEMANTIC_FIXTURE_STATS").is_some() {
        let n = cache.counts();
        eprintln!(
            "semantic-test-images: {} module{} safely replayed ({} from another build); \
             {} declaration{} kernel-checked, {} accepted from cache",
            session.hits(),
            if session.hits() == 1 { "" } else { "s" },
            session.stale_hits(),
            n.checked,
            if n.checked == 1 { "" } else { "s" },
            n.hits,
        );
    }
    elab
}

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
        Succ(k, ih) => @Nat::cong_succ(add(k, 0), k, ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m as λ z => add(z, Succ(n)) = Succ(add(z, n)) {
        Zero => refl,
        Succ(k, ih) => @Nat::cong_succ(add(k, Succ(n)), Succ(add(k, n)), ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m as λ z => add(z, n) = add(n, z) {
        Zero => @sym(add(n, 0), n, add_zero(n)),
        Succ(k, ih) => @trans(
            Succ(add(k, n)),
            Succ(add(n, k)),
            add(n, Succ(k)),
            @Nat::cong_succ(add(k, n), add(n, k), ih),
            @sym(add(n, Succ(k)), Succ(add(n, k)), add_succ(n, k))
        ),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a as λ z => add(add(z, b), c) = add(z, add(b, c)) {
        Zero => refl,
        Succ(k, ih) => @Nat::cong_succ(add(add(k, b), c), add(k, add(b, c)), ih),
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

/// `modules` elaborated from source on top of the prelude **once per test
/// process**, and every call a fork of that checked state
/// (`issues/suite-tests-reelaborate-library-modules.md`).
///
/// The checks are exactly the hand-written loop's — the current frontend
/// and the real kernel over every module's source, no image replay — only
/// not repeated by every test of the binary: `list` alone was re-elaborated
/// by 108 tests in about twenty binaries. A fork shares the committed prefix
/// and nothing else (`SemanticImage::elaborator`), so a test's own modules,
/// mutations and controls cannot leak into another test. A module that does
/// not check panics with its rendered error, as each loop did.
pub fn library(modules: &[(&str, &str)]) -> heather_elab::Elaborator {
    use std::sync::{Mutex, OnceLock};
    static BUILT: OnceLock<Mutex<Vec<(u64, heather_elab::SemanticImage)>>> = OnceLock::new();
    let mut key = Fnv1a::new();
    for (name, src) in modules {
        key.write(name.as_bytes());
        key.write(&[0]);
        key.write(src.as_bytes());
        key.write(&[0]);
    }
    let key = key.0;
    // Held across the build, so parallel tests of one binary wait for the
    // first rather than all elaborating the same prefix at once.
    let mut built = BUILT.get_or_init(|| Mutex::new(Vec::new())).lock().unwrap_or_else(|p| p.into_inner());
    if let Some((_, image)) = built.iter().find(|(k, _)| *k == key) {
        return image.elaborator();
    }
    let mut e = heather_elab::Elaborator::with_prelude().expect("prelude");
    for (name, src) in modules {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check:\n{}", err.render(src));
        }
    }
    let image = e.semantic_image();
    let fork = image.elaborator();
    built.push((key, image));
    fork
}

/// A mutated emission (or mutated-library emission) elaborated into the
/// `ir_v1` module, required to be **refused, and refused by the kernel**.
///
/// Shared by the six `certgen_*` test binaries, which is a departure from this
/// file's usual rule that harness helpers stay file-local: the six had
/// byte-identical private copies, and the guard below is exactly the kind of
/// thing that gets added to one copy and not the other five.
///
/// The guard (`issues/certgen-emission-idiomatic-style.md`, inherited from the
/// datarepr round's `refused`): a control mutates generated source with a
/// string edit, so a pattern that has drifted away from the emission can leave
/// the text **unparseable** — and then the control is green for a reason that
/// has nothing to do with the property it names. A `ParseError` is therefore a
/// failure here, not a pass. `assert_ne!` on the mutation catches a pattern
/// that matched *nothing*; this catches a pattern that matched and cut.
pub fn refuted_by_the_kernel(e: &mut heather_elab::Elaborator, src: &str, what: &str) {
    match e.elab_module_source("ir_v1", src) {
        Ok(()) => panic!("{what} elaborated, but it must fail"),
        Err(heather_elab::ElabError::Parse(p)) => panic!(
            "{what} was refused by the PARSER, so this control proves nothing \
             about the mutation: {}\n{src}",
            p.msg
        ),
        Err(_) => {}
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

/// The `Bin` carrier and its lemmas, without a `datarepr` declaration: the
/// half [`BIN_REPR`] and [`BIN_CANON`] share. Two reprs of `Nat` cannot
/// coexist in one elaborator (v1 is one repr per spec type), so the shared
/// part is a macro and each repr concatenates its own declaration onto it —
/// a second copy of the carrier would drift from the obligations it is the
/// fixture for, which is the whole reason this file exists.
macro_rules! bin_base {
    () => {
        r#"
inductive Bin { BNil, B0(b: Bin), B1(b: Bin) }

fn double(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(double(k))) } }

// Little-endian bits, least significant first. `B0(BNil)` and `BNil` both
// denote zero: `abs` is not injective, and nothing requires it to be.
fn bin_abs(r: Bin) -> Nat {
    match r {
        BNil => Zero,
        B0(b) => double(bin_abs(b)),
        B1(b) => Succ(double(bin_abs(b))),
    }
}

fn bin_inv(r: Bin) -> Type { Zero = Zero }

fn binc(r: Bin) -> Bin {
    match r { BNil => B1(BNil), B0(b) => B1(b), B1(b) => B0(binc(b)) }
}

theorem cong_double({a: Nat}, {b: Nat}, p: a = b): double(a) = double(b) {
    j(p, λ y q => double(a) = double(y), refl)
}

// The commutation law for `Succ`'s image. The carry case is the only one with
// content: it is where `binc` recurses and where `double(Succ n)` has to
// unfold on the other side.
theorem bin_succ_abs(r: Bin): bin_abs(binc(r)) = Succ(bin_abs(r)) {
    match r { BNil => refl, B0(b) => refl, B1(b) => cong_double(bin_succ_abs(b)) }
}

// `bin_succ_abs` is the ONE law both reprs cite, as an applied clause
// (`Succ_abs := bin_succ_abs(a0)`, `issues/datarepr-law-clause-inv-binders.md`):
// a law's hypothesis is the repr's own `inv`, and `BinNat`'s equation-shaped
// one is not convertible with `BinMin`'s defaulted `True`, so as whole-Π
// values this fixture had to carry the same theorem twice, differing only in
// a binder neither body mentioned.

// `Nat`'s recursor, by hand: `match` is a form and not a global, so the
// anchor's statement needs a name. Definitionally the generated
// `BinNat_spec_rec`, which is what lets the hand-written law below discharge
// the generated obligation.
fn nat_rec_(B: Type, z: B, s: (a: Nat) -> (b: B) -> B, x: Nat) -> B {
    match x { Zero => z, Succ(k) => s(k, nat_rec_(B, z, s, k)) }
}

fn bin_of_nat(n: Nat) -> Bin { match n { Zero => BNil, Succ(m) => binc(bin_of_nat(m)) } }

theorem bin_roundtrip(m: Nat): bin_abs(bin_of_nat(m)) = m {
    match m {
        Zero => refl,
        Succ(k) => trans(bin_succ_abs(bin_of_nat(k)), Nat::cong_succ(bin_roundtrip(k))),
    }
}

// The anchor. Slow on purpose (§1.1): it goes through the spec value, which
// is exactly what the cost basis exists to bypass.
fn bin_fold(B: Type, s0: B, s1: (a0: Bin) -> (b0: B) -> B, r: Bin) -> B {
    nat_rec_(B, s0, λ m b => s1(bin_of_nat(m), b), bin_abs(r))
}

theorem natrec_cong(B: Type, z: B, s1: (a: Nat) -> (b: B) -> B,
                    s2: (a: Nat) -> (b: B) -> B,
                    h: (a: Nat) -> (b: B) -> s1(a, b) = s2(a, b), n: Nat):
    nat_rec_(B, z, s1, n) = nat_rec_(B, z, s2, n)
{
    match n {
        Zero => refl,
        Succ(k) => trans(
            j(natrec_cong(B, z, s1, s2, h, k),
              λ y q => s1(k, nat_rec_(B, z, s1, k)) = s1(k, y), refl),
            h(k, nat_rec_(B, z, s2, k))),
    }
}

theorem bin_fold_law(B: Type, s0: B, s1: (a0: Nat) -> (b0: B) -> B, r: Bin,
                     h: (Zero = Zero)):
    bin_fold(B, s0, λ a0 b0 => s1(bin_abs(a0), b0), r)
      = nat_rec_(B, s0, s1, bin_abs(r))
{
    natrec_cong(B, s0, λ m b => s1(bin_abs(bin_of_nat(m)), b), s1,
                λ a b =>
                    j(bin_roundtrip(a),
                      λ y q => s1(bin_abs(bin_of_nat(a)), b) = s1(y, b), refl),
                bin_abs(r))
}

theorem cong_bin_abs({a: Bin}, {b: Bin}, p: a = b): bin_abs(a) = bin_abs(b) {
    j(p, λ y q => bin_abs(a) = bin_abs(y), refl)
}
"#
    };
}

/// `Bin` as a repr of `Nat` — the v1 stretch of `docs/datarepr-design.md`
/// §5.1 item 4, and the one non-identity repr the suite has. Shared rather
/// than copied because `datarepr.rs` and `reprgen.rs` both pin it and a
/// private copy would drift from the obligations it is the fixture for.
///
/// Its `inv` is *written* and trivially true (`Zero = Zero`, an equation with
/// no content), which is what makes [`BIN_CANON`] worth having — and, since
/// `issues/true-prop-trivial-hypotheses.md`, what makes it the control that a
/// repr whose `inv` is written is untouched by the defaulted `inv`'s flip to
/// the prelude `True`. [`BIN_MIN`] is the flipped side.
pub const BIN_REPR: &str = concat!(
    bin_base!(),
    r#"
datarepr BinNat for Nat {
    R := Bin,
    abs := bin_abs,
    inv := bin_inv,
    mk Zero := BNil,
    mk Succ := binc,
    Succ_abs := bin_succ_abs(a0),
    fold := bin_fold,
    fold_law := bin_fold_law,
}
"#
);

/// The same carrier under a **canonical-form invariant** (design §1.2): `r` is
/// the representative `bin_of_nat` builds for its own value, which rules out
/// `Bin`'s leading zeros and makes `abs` injective on `inv`-satisfying values.
///
/// It exists for one reason: at a trivial `inv` every `inv` obligation in a
/// transfer is inhabited without looking at anything, and the machinery that
/// carries `inv` proofs around is untested. Here `Succ_inv` genuinely *consumes* its hypothesis, so
/// a transfer's `inv`-preservation lemma has content — the third lemma of the
/// repr-typed-result stage (§3.3, as-landed).
pub const BIN_CANON: &str = concat!(
    bin_base!(),
    r#"
// "`r` is canonical": the round-trip through the spec value returns `r`
// itself. `B0(BNil)` is not, `BNil` is.
fn bin_canon(r: Bin) -> Type { bin_of_nat(bin_abs(r)) = r }

theorem bin_succ_abs_canon(a0: Bin, h0: bin_canon(a0)):
    bin_abs(binc(a0)) = Succ(bin_abs(a0)) { bin_succ_abs(a0) }

// The closure law that needs its hypothesis: `binc` of a canonical value is
// canonical, *because* the argument was.
theorem bin_canon_succ(a0: Bin, h0: bin_canon(a0)): bin_canon(binc(a0)) {
    trans(j(bin_succ_abs(a0),
            λ y q => bin_of_nat(bin_abs(binc(a0))) = bin_of_nat(y), refl),
          j(h0, λ y q => binc(bin_of_nat(bin_abs(a0))) = binc(y), refl))
}

// The anchor law, restated under the stronger `inv` (which it does not use).
theorem bin_fold_law_canon(B: Type, s0: B, s1: (a0: Nat) -> (b0: B) -> B, r: Bin,
                           h: bin_canon(r)):
    bin_fold(B, s0, λ a0 b0 => s1(bin_abs(a0), b0), r)
      = nat_rec_(B, s0, s1, bin_abs(r))
{ bin_fold_law(B, s0, s1, r, refl) }

datarepr BinC for Nat {
    R := Bin,
    abs := bin_abs,
    inv := bin_canon,
    mk Zero := BNil,
    mk Succ := binc,
    Succ_abs := bin_succ_abs_canon,
    Succ_inv := bin_canon_succ,
    fold := bin_fold,
    fold_law := bin_fold_law_canon,
}
"#
);

/// The **minimal** repr the clause defaults make writable
/// (`issues/repr-fold-via-abs-default.md`): the carrier, `abs`, one `mk` per
/// constructor, and the one law that is not `refl`. `inv` defaults to `True`
/// and `fold` to the fold *through* `abs` — the shape [`BIN_REPR`] writes by
/// hand, generated instead, together with the embedding and the two lemmas its
/// anchor law rests on.
///
/// It shares [`bin_base`] with the other two, so the hand-written `bin_fold`
/// and `bin_of_nat` are in scope and unused here on purpose: what the fixture
/// pins is that the generated ones are *not* them.
pub const BIN_MIN: &str = concat!(
    bin_base!(),
    r#"
datarepr BinMin for Nat {
    R := Bin,
    abs := bin_abs,
    mk Zero := BNil,
    mk Succ := binc,
    Succ_abs := bin_succ_abs(a0),
}
"#
);

/// A repr of `Nat` whose `fold` recurses on the **carrier** — deliberately not
/// `spec_rec ∘ abs` — under a canonical-form `inv`.
///
/// It is the control point design §3.3's as-landed note 5 records as missing:
/// where `fold` is defined through `abs`, both sides of `fold_law` are
/// convertible for an algebra that ignores the spec child, so `refines_inv`'s
/// transport *direction* is unobservable and deleting its `sym` still checks.
/// Here the two sides are two different stuck terms, and the direction is real.
/// The canonical `inv` is the other half of what makes it observable: at
/// `inv = True` the transported motive is constant and any direction proves it.
pub const UNARY_CANON: &str = r#"
inductive Un { UZ, US(u: Un) }

fn nat_rec_(B: Type, z: B, s: (a: Nat) -> (b: B) -> B, x: Nat) -> B {
    match x { Zero => z, Succ(k) => s(k, nat_rec_(B, z, s, k)) }
}

fn un_abs(r: Un) -> Nat { match r { UZ => Zero, US(u) => Succ(un_abs(u)) } }
fn un_of_nat(n: Nat) -> Un { match n { Zero => UZ, Succ(m) => US(un_of_nat(m)) } }

// Every `Un` is canonical — `abs` is injective here — but the proposition is
// still about `r`, which is what `True` is not.
fn un_canon(r: Un) -> Type { un_of_nat(un_abs(r)) = r }

theorem un_canon_succ(a0: Un, h0: un_canon(a0)): un_canon(US(a0)) {
    j(h0, λ y q => US(un_of_nat(un_abs(a0))) = US(y), refl)
}

fn un_fold(B: Type, s0: B, s1: (a0: Un) -> (b0: B) -> B, r: Un) -> B {
    match r { UZ => s0, US(u) => s1(u, un_fold(B, s0, s1, u)) }
}

// The anchor law holds without the invariant, and the clause restates it under
// one: the recursive call would otherwise owe `un_canon` of the child, which
// only injectivity of `US` gives back.
theorem un_fold_law_free(B: Type, s0: B, s1: (a0: Nat) -> (b0: B) -> B, r: Un):
    un_fold(B, s0, λ a0 b0 => s1(un_abs(a0), b0), r)
      = nat_rec_(B, s0, s1, un_abs(r))
{
    match r {
        UZ => refl,
        US(u) => j(un_fold_law_free(B, s0, s1, u),
                   λ y q => s1(un_abs(u), un_fold(B, s0,
                                λ a0 b0 => s1(un_abs(a0), b0), u))
                              = s1(un_abs(u), y), refl),
    }
}

theorem un_fold_law(B: Type, s0: B, s1: (a0: Nat) -> (b0: B) -> B, r: Un, h: un_canon(r)):
    un_fold(B, s0, λ a0 b0 => s1(un_abs(a0), b0), r)
      = nat_rec_(B, s0, s1, un_abs(r))
{ un_fold_law_free(B, s0, s1, r) }

datarepr UnC for Nat {
    R := Un,
    abs := un_abs,
    inv := un_canon,
    mk Zero := UZ,
    mk Succ := US,
    Succ_inv := un_canon_succ,
    fold := un_fold,
    fold_law := un_fold_law,
}
"#;

/// `add` at `Bin`: the derived body out of the fold anchor, its certificate,
/// and the congruence the via-derived route needs. Appended to
/// [`BIN_REPR`], never used alone.
pub const BIN_ADD: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }

fn bin_add_derived(ra: Bin, rb: Bin) -> Bin {
    bin_fold(Bin, ra, λ t acc => binc(acc), rb)
}

// `binc` iterated `n` times commutes with `abs` into `add`. The only
// induction the cost basis needs here.
theorem bin_iter_abs(ra: Bin, n: Nat):
    bin_abs(nat_rec_(Bin, ra, λ a b => binc(b), n))
      = add(bin_abs(ra), n)
{
    match n {
        Zero => refl,
        Succ(k) => trans(
            bin_succ_abs(nat_rec_(Bin, ra, λ a b => binc(b), k)),
            Nat::cong_succ(bin_iter_abs(ra, k))),
    }
}

theorem bin_add_derived_refines(ra: Bin, rb: Bin, h0: (Zero = Zero), h1: (Zero = Zero)):
    bin_abs(bin_add_derived(ra, rb)) = add(bin_abs(ra), bin_abs(rb))
{ bin_iter_abs(ra, bin_abs(rb)) }

theorem bin_add_derived_inv(ra: Bin, rb: Bin, h0: (Zero = Zero), h1: (Zero = Zero)):
    bin_inv(bin_add_derived(ra, rb)) { refl }

"#;
