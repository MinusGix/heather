//! NON-`Nat` EMBEDDINGS — the certifying generator's fragment beyond `Nat`
//! (`docs/certgen-non-nat-embeddings-design.md`,
//! `docs/certifying-generator-design.md` §8 item 2).
//!
//! A fragment function's *result* type may be a tier-0 ENUMERATION: a
//! non-recursive, unindexed, unparameterized `inductive` with at least one
//! constructor and no constructor fields. Parameters stay `Nat` and recursion
//! stays structural on a `Nat`, for the lowering reason the design doc's §2.1
//! records (a match on an inductive parameter is `Term::Case`, with an
//! `El(D#tycode^δ)` motive and Σ-projection arm binders).
//!
//! What the round had to widen, and where:
//!
//!   * `lib/certgen_code.hthr` — the walker's `tm_triv`/`tm_pair`/`tm_inl`/
//!     `tm_inr` arms (convention 4) and the signature checker's
//!     `ty_unit`/`ty_sigma`/`ty_sum` arms. Both are the *analysis*, and the
//!     frozen-walker rule (`issues/retire-rust-transcriber.md`) says a new
//!     fragment feature lands in-language only. The file's own `refl`
//!     theorems pin both, one layer below this binary.
//!   * `lib/certgen_cert.hthr` — **nothing**. A constructor tag is already a
//!     `Nat` field of `CCon`, and the induction is still over the scrutinized
//!     `Nat` parameter, so the certificate fold absorbed the feature with zero
//!     edits. That is the strongest available reading of
//!     `docs/certgen-cert-expression-design.md`'s perturbability claim.
//!   * `crates/elab/src/certgen.rs` — names and rendering only: the result
//!     type's description (`ResTy`), the emitted `embed_T`, the per-signature
//!     record, and per-slot embeddings in the proof text.
//!
//! **A binary of its own**, for the reason `issues/certgen-harness-cost.md`
//! calls the free lever: `scripts/test`'s `ulimit -t` is per *process*, and
//! `crates/elab/tests/certgen.rs` is already close to it. Every test here
//! builds its own `Elaborator` anyway, so the split costs nothing and buys a
//! whole 300-second rail.

use heather_elab::certgen::{generate_in_language, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const CODE: &str = include_str!("../../../lib/certgen_code.hthr");
const CERT: &str = include_str!("../../../lib/certgen_cert.hthr");

/// Items a generated emission needs beyond the declarations prefix, in
/// dependency (file-consistent) order — the same slice
/// `crates/elab/tests/certgen.rs` takes.
const SUPPORT_ITEMS: [&str; 14] = [
    "dbl",
    "BindInv",
    "k_bind_inv",
    "k_bind_mono",
    "step_mono",
    "eval_mono_succ",
    "eval_mono_plus",
    "fuel_monotone",
    "Converges",
    "ret_conv",
    "letcon_conv",
    "letcall_conv",
    "letmatch_conv",
    "CompileNat2",
];

fn support() -> String {
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    let mut s = LIB[..cut].to_string();
    let file = parse_file(LIB).expect("the library parses");
    for name in SUPPORT_ITEMS {
        let span = file
            .items
            .iter()
            .find_map(|i| match i {
                Item::Inductive(ind) if ind.name == name => Some(ind.span),
                Item::Decl(d) if d.name == name => Some(d.span),
                _ => None,
            })
            .unwrap_or_else(|| panic!("the library declares {name}"));
        s.push('\n');
        s.push_str(&LIB[span.start..span.end]);
        s.push('\n');
    }
    s
}

fn decl_of(src: &str) -> Decl {
    let file = parse_file(src).unwrap_or_else(|e| panic!("test fn parses: {e:?}"));
    assert_eq!(file.items.len(), 1);
    file.items.into_iter().next().unwrap().into_decl()
}

fn elab(e: &mut Elaborator, src: &str, what: &str) {
    e.elab_module_source("ir_v1", src)
        .unwrap_or_else(|err| panic!("{what}:\n{}", err.render(src)));
}

fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    if e.elab_module_source("ir_v1", src).is_ok() {
        panic!("{what} elaborated, but it must fail");
    }
}

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

// ---------------------------------------------------------------------------
// The fixture types and functions.
//
// Declared here rather than reused from `bool`, because imports are not
// transitive and these tests elaborate as module `ir_v1`. Between them the
// types cover the shapes the widening turns on: two constructors, and three
// (so a tag no `Nat` body can produce). `Peek` is the decline: a constructor
// with a field, which this stage defers.

const TYPES: &str = "\
inductive Flag { Off, On }
inductive Sign3 { SNeg, SZero, SPos }
inductive Peek { PNone, PSome(k: Nat) }
";

const ISZERO: &str = "fn is_zero(n: Nat) -> Flag { match n { Zero => On, Succ(k) => Off } }";
const SIGN: &str = "fn sign(n: Nat) -> Sign3 { match n { Zero => SZero, Succ(k) => SPos } }";
const PEEK: &str = "fn peek(n: Nat) -> Peek { match n { Zero => PNone, Succ(k) => PSome(k) } }";
/// A cross-function call whose callee returns a non-`Nat` (§2.3, §8): the
/// caller's signature is in the fragment, and the decline is the MARKER pass's
/// — a callee marker is a closed `Nat -> … -> Nat` chain, so a callee outside
/// that signature has no marker to stand for it.
const VIAADD: &str =
    "fn viaflag(n: Nat) -> Flag { match n { Zero => On, Succ(k) => is_zero(k) } }";
/// A **self-call at a non-`Nat` result**: the induction hypothesis is consumed
/// at goal `VCons(Flag_gen_embed(tt(gk)), VNil)`, which is the one place the
/// new embedding meets the ∃-kit's `letcall_conv`.
const TT: &str = "fn tt(n: Nat) -> Flag { match n { Zero => On, Succ(k) => tt(k) } }";

// ---------------------------------------------------------------------------
// THE LAYOUT INTERFACE for non-`Nat` results, pinned as literals — the same
// discipline `crates/elab/tests/certgen.rs`'s `IR_*` constants carry since the
// oracle was retired.

/// Two constructors: `On` is tag 1 because it is declared second, which is the
/// lowering's `inr(inl(·))` order — the same order `Flag_gen_embed` writes.
const IR_ISZERO: &str = "\
is_zero_gen_arm_zero() = LetCon(1, RNil, Ret(RCons(0, RNil)))
is_zero_gen_arm_succ() = LetCon(0, RNil, Ret(RCons(0, RNil)))
is_zero_gen_body() = LetMatch(0, Arm(is_zero_gen_arm_zero(), Arm(is_zero_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// Three constructors, so a tag of 2 — which no `Nat` transcription can emit.
const IR_SIGN: &str = "\
sign_gen_arm_zero() = LetCon(1, RNil, Ret(RCons(0, RNil)))
sign_gen_arm_succ() = LetCon(2, RNil, Ret(RCons(0, RNil)))
sign_gen_body() = LetMatch(0, Arm(sign_gen_arm_zero(), Arm(sign_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// The transcriptions and the declines, on the *declarations* prefix alone —
/// nothing here elaborates a certificate, so it is the cheap half.
#[test]
fn nonnat_transcriptions_and_declines() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    elab(&mut e, &LIB[..cut], "declarations prefix");
    elab(&mut e, CODE, "lib/certgen_code.hthr");
    elab(&mut e, CERT, "lib/certgen_cert.hthr");
    elab(&mut e, TYPES, "the non-`Nat` result types");
    elab(&mut e, ISZERO, "fn is_zero");
    elab(&mut e, SIGN, "fn sign");

    for (d, want) in [(decl_of(ISZERO), IR_ISZERO), (decl_of(SIGN), IR_SIGN)] {
        let em = generate_in_language(&e, &d, &GenCtx::new())
            .unwrap_or_else(|r| panic!("{} declined: {r}", d.name));
        assert_eq!(em.ir_body, want, "{} transcribes differently", d.name);
        assert_eq!(em.closure, vec![d.name.clone()], "{}'s closure", d.name);
        // The derived artifact travels with the emission, once per type.
        assert!(
            em.support.iter().any(|(k, _)| k.starts_with("embed:")),
            "{} carries no `embed_T`",
            d.name
        );
    }

    // A constructor WITH A FIELD is declined by the LIBRARY's `check_sig` —
    // `sig_sigma` refuses a payload with a value in it — and is *not* a
    // disagreement with the Rust residue, which is the agreement property
    // asserted from the negative side.
    {
        elab(&mut e, PEEK, "fn peek");
        let d = decl_of(PEEK);
        let Err(msg) = generate_in_language(&e, &d, &GenCtx::new()) else {
            panic!("`peek`'s signature must decline")
        };
        assert!(msg.contains("in-language signature checker"), "{msg}");
        assert!(!msg.contains("disagreement"), "{msg}");
    }

    // A RIM decline (design doc §§2.3, 8): cross-function composition at a
    // non-`Nat` result is deferred, and the boundary is the callee-marker
    // convention — a marker is a closed `Nat -> … -> Nat` chain, so a callee
    // returning anything else has none. The caller's own signature is in the
    // fragment; the decline names the callee.
    {
        let d = decl_of(VIAADD);
        elab(&mut e, VIAADD, "cross-function non-`Nat` fixture");
        let Err(msg) = generate_in_language(&e, &d, &GenCtx::new()) else {
            panic!("`viaflag` must decline")
        };
        assert!(msg.contains("is_zero"), "{msg}");
        assert!(!msg.contains("disagreement"), "{msg}");
    }
}

/// The end-to-end acceptance: three generated `Compile` instances over two
/// non-`Nat` result types — a two-constructor one, a three-constructor one
/// (so a tag of 2), and a self-call at a non-`Nat` result — every one
/// elaborated and kernel-checked, plus the mutation controls.
///
/// The four axes of `docs/testing-generated-terms.md`: the exactness fixtures
/// run at *literal* arguments while every invariant is *open* in its parameter
/// and in `tail`; the instance is a **checking** position against the
/// per-signature record at the declared spec function, which is where a wrong
/// embedding dies; and the two mutations below are the negative controls.
#[test]
fn nonnat_emissions_and_controls() {
    let mut e = base();
    let sup = support();
    elab(&mut e, &sup, "support prelude");
    elab(&mut e, CODE, "lib/certgen_code.hthr");
    elab(&mut e, CERT, "lib/certgen_cert.hthr");
    elab(&mut e, TYPES, "the non-`Nat` result types");
    elab(&mut e, ISZERO, "fn is_zero");
    elab(&mut e, SIGN, "fn sign");
    elab(&mut e, TT, "fn tt");

    let mut ctx = GenCtx::new();
    let mut support_done: Vec<String> = Vec::new();
    for d in [decl_of(ISZERO), decl_of(SIGN), decl_of(TT)] {
        let em = generate_in_language(&e, &d, &ctx)
            .unwrap_or_else(|r| panic!("{} declined: {r}", d.name));
        for (key, text) in &em.support {
            if !support_done.contains(key) {
                elab(&mut e, text, key);
                support_done.push(key.clone());
            }
        }
        elab(&mut e, &em.text, &format!("emission for {}", em.name));
        ctx.push(em);
    }

    // One `embed_T` per TYPE and one record per SIGNATURE — `is_zero` and `tt`
    // share both, which is what the support-key dedup is for.
    assert!(support_done.contains(&"embed:Flag".to_string()), "{support_done:?}");
    assert!(support_done.contains(&"embed:Sign3".to_string()), "{support_done:?}");
    assert!(support_done.contains(&"record:CompileNat1Flag".to_string()), "{support_done:?}");
    assert_eq!(support_done.iter().filter(|k| *k == "embed:Flag").count(), 1);

    let iz = &ctx_get(&ctx, "is_zero").text;
    assert!(iz.contains("CompileNat1Flag(is_zero)"), "{iz}");
    assert!(iz.contains("Flag_gen_embed(is_zero("), "{iz}");
    assert!(!iz.contains("embed_nat(is_zero"), "{iz}");
    // The `Succ` arm's field is a `Nat` whatever the result type is: recursion
    // is structural on a `Nat` parameter, so `gk` never changes embedding.
    assert!(ctx_get(&ctx, "tt").text.contains("VCons(embed_nat(gk), VNil)"));
    // The self-call at a non-`Nat` result consumes the induction hypothesis at
    // the new embedding's goal.
    let tt = &ctx_get(&ctx, "tt").text;
    assert!(tt.contains("Flag_gen_embed(tt(gk))"), "{tt}");

    // (a) a wrong constructor tag: the body builds `Off` where every emitted
    // proof says `On`, so the exactness fixture's `refl` refuses it.
    let good = &ctx_get(&ctx, "is_zero").text;
    let m = good
        .replace("is_zero_gen", "is_zerom1_gen")
        .replacen("LetCon(1, RNil", "LetCon(0, RNil", 1);
    assert!(
        m.contains("is_zerom1_gen_arm_zero() -> Ir { LetCon(0, RNil"),
        "the mutation must apply"
    );
    refuted(&mut e, &m, "wrong constructor tag at a non-`Nat` result");

    // (b) a perturbed fixture claim: the fixture runs at 2, where `is_zero`
    // is `Off`, and the mutant claims the answer at 0, where it is `On`. A
    // complete, plausible, FALSE statement — refused by its own `refl`.
    let m = good
        .replace("is_zero_gen", "is_zerom2_gen")
        .replacen("Flag_gen_embed(is_zero(2))", "Flag_gen_embed(is_zero(0))", 1);
    assert!(m.contains("Flag_gen_embed(is_zero(0))"), "the mutation must apply");
    refuted(&mut e, &m, "wrong fixture result at a non-`Nat` result");
}

fn ctx_get<'a>(ctx: &'a GenCtx, name: &str) -> &'a heather_elab::certgen::Emission {
    ctx.iter().find(|e| e.name == name).expect("emission present")
}
