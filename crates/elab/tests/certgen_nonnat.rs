//! NON-`Nat` EMBEDDINGS — the certifying generator's fragment beyond `Nat`
//! (`docs/certgen-non-nat-embeddings-design.md`,
//! `docs/certifying-generator-design.md` §8 item 2).
//!
//! A fragment function's *result* type may be a tier-0 ENUMERATION: a
//! non-recursive, unindexed, unparameterized `inductive` with at least one
//! constructor, whose constructors may take `Nat` FIELDS
//! (`docs/certgen-ctor-fields-design.md`, 2026-08-13 — the stage §2.2 of the
//! non-`Nat` doc cut on a cost law that two elaborator spelling rounds have
//! since cut). This binary's fixtures keep all-`Nat` parameters and
//! `Nat`-structural recursion; the parameter position widened later — tier-1
//! inductives (`certgen_tier1.rs`) and tier-0 enumerations
//! (`certgen_t0param.rs`) — without moving a byte here, which is this file's
//! regression role.
//!
//! The fields stage also lands CROSS-FUNCTION COMPOSITION at a non-`Nat`
//! result (non-`Nat` §2.3, deferred there for want of a per-slot type): a
//! foreign call's temporary is a `Nat` and the returned one is the result
//! type, which is a positional rule rather than inference, and a `Nat`
//! temporary now has somewhere to be *used* — a constructor field.
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

mod support;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
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

/// `add`, from `lib/std/nat.hthr` — the callee the cross-function fixture
/// composes with, and the only emission here whose result is a `Nat`.
fn nat_decl(name: &str) -> Decl {
    parse_file(NAT)
        .expect("`nat` parses")
        .items
        .into_iter()
        .find_map(|i| match i {
            Item::Decl(d) if d.name == name => Some(d),
            _ => None,
        })
        .unwrap_or_else(|| panic!("`nat` declares fn {name}"))
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

/// Shared with the other `certgen_*` binaries, and guarded: a mutation that
/// leaves the text unparseable must not read as a refusal
/// (`support::refuted_by_the_kernel`).
fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    support::refuted_by_the_kernel(e, src, what)
}

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).unwrap_or_else(|err| panic!("{}", err.render(LOGIC)));
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

// ---------------------------------------------------------------------------
// The fixture types and functions.
//
// Declared here rather than reused from `bool`, because imports are not
// transitive and these tests elaborate as module `ir_v1`. Between them the
// types cover the shapes the widening turns on: two constructors, three (so a
// tag no `Nat` body can produce), one constructor with a field and one with
// two. `Wrap` is the decline the fields stage still makes: a field at another
// INDUCTIVE, which the walker would read but `embed_T` has no embedding for.

const TYPES: &str = "\
inductive Flag { Off, On }
inductive Sign3 { SNeg, SZero, SPos }
inductive Peek { PNone, PSome(k: Nat) }
inductive Both { BNone, BSome(a: Nat, b: Nat) }
inductive Wrap { WNone, WSome(f: Flag) }
";

const ISZERO: &str = "fn is_zero(n: Nat) -> Flag { match n { Zero => On, Succ(k) => Off } }";
const SIGN: &str = "fn sign(n: Nat) -> Sign3 { match n { Zero => SZero, Succ(k) => SPos } }";
/// A constructor WITH A FIELD, the stage's headline: the arm's own binder is
/// carried into the constructor's argument list.
const PEEK: &str = "fn peek(n: Nat) -> Peek { match n { Zero => PNone, Succ(k) => PSome(k) } }";
/// TWO fields, one of them COMPUTED — the field's own instructions are merged
/// before the constructor's, and slot order is the source's.
const PACK: &str =
    "fn pack(n: Nat) -> Both { match n { Zero => BNone, Succ(k) => BSome(k, Succ(k)) } }";
/// CROSS-FUNCTION COMPOSITION at a non-`Nat` result (non-`Nat` design §2.3):
/// the foreign call binds a `Nat` temporary, which the constructor field is
/// the first place in this fragment that can *use*. The callee is written by
/// its declared name, `Nat::add`, since the std namespace refactor.
const VIAFIELD: &str =
    "fn viafield(n: Nat) -> Peek { match n { Zero => PNone, Succ(k) => PSome(Nat::add(k, k)) } }";
/// A field at ANOTHER INDUCTIVE: the walker would read it, but `embed_T` would
/// have to embed it at `Flag`'s own embedding rather than at `embed_nat`, so
/// `sig_sigma`'s field rule declines the declaration whole
/// (docs/certgen-ctor-fields-design.md §6). This is the decline the fields
/// stage puts where "a constructor with a field" used to be.
const HOLDS: &str = "fn holds(n: Nat) -> Wrap { match n { Zero => WNone, Succ(k) => WNone } }";
/// A cross-function call whose CALLEE returns a non-`Nat` (§2.3, §8): the
/// caller's signature is in the fragment, and the decline is the MARKER pass's
/// — a callee marker is a closed `Nat -> … -> Nat` chain, so a callee outside
/// that signature has no marker to stand for it. Unchanged by the fields
/// stage, which widened the *caller* side only.
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

/// A constructor with ONE field: the arm's binder `k` is at distance 0, and
/// the tag-1 instruction carries it as its single argument. Compare
/// `IR_ISZERO`'s `LetCon(1, RNil, …)` — same tag, one argument more.
const IR_PEEK: &str = "\
peek_gen_arm_zero() = LetCon(0, RNil, Ret(RCons(0, RNil)))
peek_gen_arm_succ() = LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil)))
peek_gen_body() = LetMatch(0, Arm(peek_gen_arm_zero(), Arm(peek_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// TWO fields, the second computed: `Succ(k)` is its own instruction, and the
/// constructor reads `(k, Succ(k))` as `(1, 0)` — the field ORDER, which is
/// what the perturbed-library control in `certgen_controls.rs` breaks.
const IR_PACK: &str = "\
pack_gen_arm_zero() = LetCon(0, RNil, Ret(RCons(0, RNil)))
pack_gen_arm_succ() = LetCon(1, RCons(0, RNil), LetCon(1, RCons(1, RCons(0, RNil)), Ret(RCons(0, RNil))))
pack_gen_body() = LetMatch(0, Arm(pack_gen_arm_zero(), Arm(pack_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// A FOREIGN CALL feeding a field: the two-member closure `[Nat::add, viafield]`
/// puts `add` at index 0, and the constructor reads the call's result.
const IR_VIAFIELD: &str = "\
viafield_gen_arm_zero() = LetCon(0, RNil, Ret(RCons(0, RNil)))
viafield_gen_arm_succ() = LetCall(0, RCons(0, RCons(0, RNil)), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))
viafield_gen_body() = LetMatch(0, Arm(viafield_gen_arm_zero(), Arm(viafield_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// The transcriptions and the declines, on the *declarations* prefix alone —
/// nothing here elaborates a certificate, so it is the cheap half.
#[test]
fn nonnat_transcriptions_and_declines() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    // Checked-in prefix through the shared declaration cache; the fixture
    // types and everything generated face the kernel unconditionally.
    support::with_decl_cache(&mut e, |e| {
        elab(e, &LIB[..cut], "declarations prefix");
        elab(e, CODE, "lib/certgen_code.hthr");
        elab(e, CERT, "lib/certgen_cert.hthr");
    });
    elab(&mut e, TYPES, "the non-`Nat` result types");
    elab(&mut e, ISZERO, "fn is_zero");
    elab(&mut e, SIGN, "fn sign");
    elab(&mut e, PEEK, "fn peek");
    elab(&mut e, PACK, "fn pack");

    for (d, want) in [
        (decl_of(ISZERO), IR_ISZERO),
        (decl_of(SIGN), IR_SIGN),
        (decl_of(PEEK), IR_PEEK),
        (decl_of(PACK), IR_PACK),
    ] {
        let em = generate_in_language(&e, &d, &GenCtx::new())
            .unwrap_or_else(|r| panic!("{} declined: {r}", d.name));
        assert_eq!(em.ir_body, want, "{} transcribes differently", d.name);
        assert_eq!(em.closure_names(), vec![d.name.clone()], "{}'s closure", d.name);
        // The derived artifact travels with the emission, once per type.
        assert!(
            em.support.iter().any(|(k, _)| k.starts_with("embed:")),
            "{} carries no `embed_T`",
            d.name
        );
    }

    // `embed_T` embeds each field at `embed_nat`, in declaration order — the
    // scheme `ResTy::embed_text` was written for one stage before fields
    // landed and inherited unchanged (docs/certgen-ctor-fields-design.md §7).
    {
        let em = generate_in_language(&e, &decl_of(PACK), &GenCtx::new()).expect("pack");
        let (_, embed) = em
            .support
            .iter()
            .find(|(k, _)| k == "embed:Both")
            .expect("`Both` carries an embedding");
        assert!(embed.contains("BNone => VCon(0, VNil)"), "{embed}");
        assert!(
            embed.contains("BSome(gf0, gf1) => VCon(1, VCons(embed_nat(gf0), VCons(embed_nat(gf1), VNil)))"),
            "{embed}"
        );
    }

    // ONE FLIP, recorded rather than hidden (the same discipline the non-`Nat`
    // round used for `tocmp`): `peek` was this file's "a constructor with a
    // field declines" fixture and is a POSITIVE above. Its replacement is a
    // decline the fields stage still makes — a field at another inductive,
    // which `embed_T` has no embedding for — and it is the LIBRARY's verdict,
    // not a disagreement with the Rust residue, which is the agreement
    // property asserted from the negative side.
    {
        elab(&mut e, HOLDS, "fn holds");
        let d = decl_of(HOLDS);
        let Err(msg) = generate_in_language(&e, &d, &GenCtx::new()) else {
            panic!("`holds`'s signature must decline")
        };
        assert!(msg.contains("in-language signature checker"), "{msg}");
        assert!(!msg.contains("disagreement"), "{msg}");
    }

    // A RIM decline (design doc §§2.3, 8), and the one the fields stage did
    // NOT widen: the caller side of cross-function composition landed, the
    // callee side did not, and the boundary is the callee-marker convention —
    // a marker is a closed `Nat -> … -> Nat` chain, so a callee returning
    // anything else has none. The caller's own signature is in the fragment;
    // the decline names the callee.
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

/// The end-to-end acceptance: generated `Compile` instances over four
/// non-`Nat` result types — a two-constructor one, a three-constructor one (so
/// a tag of 2), a self-call at a non-`Nat` result, a constructor with a FIELD,
/// one with two fields of which one is computed, and a constructor field fed
/// by a CROSS-FUNCTION call — every one elaborated and kernel-checked, plus
/// the mutation controls.
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
    // Checked-in prefix through the shared declaration cache; the fixture
    // types and everything generated face the kernel unconditionally.
    support::with_decl_cache(&mut e, |e| {
        elab(e, &sup, "support prelude");
        elab(e, CODE, "lib/certgen_code.hthr");
        elab(e, CERT, "lib/certgen_cert.hthr");
    });
    elab(&mut e, TYPES, "the non-`Nat` result types");
    elab(&mut e, ISZERO, "fn is_zero");
    elab(&mut e, SIGN, "fn sign");
    elab(&mut e, TT, "fn tt");
    elab(&mut e, PEEK, "fn peek");
    elab(&mut e, PACK, "fn pack");
    elab(&mut e, VIAFIELD, "fn viafield");

    let mut ctx = GenCtx::new();
    let mut support_done: Vec<String> = Vec::new();
    // `add` first: `viafield`'s foreign call needs its generated instance in
    // the context, exactly as `mul`'s does in `certgen.rs`.
    for d in [
        decl_of(ISZERO),
        decl_of(SIGN),
        decl_of(TT),
        decl_of(PEEK),
        decl_of(PACK),
        nat_decl("Nat::add"),
        decl_of(VIAFIELD),
    ] {
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

    // CONSTRUCTOR FIELDS, in the proof text: the temporary the region returns
    // is spelled at the result type's embedding and carries its field as a
    // source expression, while the field itself stays a `Nat`.
    let peek = &ctx_get(&ctx, "peek").text;
    assert!(peek.contains("Peek_gen_embed(PSome(gk))"), "{peek}");
    assert!(peek.contains("CompileNat1Peek(peek)"), "{peek}");
    let pack = &ctx_get(&ctx, "pack").text;
    assert!(pack.contains("Both_gen_embed(BSome(gk, Succ(gk)))"), "{pack}");
    // …and the computed field's OWN temporary is a `Nat`, not a `Both`: the
    // positional rule (`ProofCx::con_res`) in one assertion.
    assert!(pack.contains("VCons(embed_nat(Succ(gk)), VNil)"), "{pack}");
    assert!(!pack.contains("Both_gen_embed(Succ(gk))"), "{pack}");

    // CROSS-FUNCTION COMPOSITION at a non-`Nat` result (non-`Nat` §2.3): a
    // two-member program, the callee's invariant re-derived inside it at
    // `embed_nat`, and the caller's constructor spelled over the call.
    let vf = ctx_get(&ctx, "viafield");
    assert_eq!(vf.closure_names(), vec!["Nat::add".to_string(), "viafield".to_string()]);
    assert_eq!(vf.ir_body, IR_VIAFIELD, "viafield transcribes differently");
    assert!(vf.text.contains("Nat__add_gen_conv_in_viafield"), "{}", vf.text);
    assert!(vf.text.contains("Peek_gen_embed(PSome(Nat::add(gk, gk)))"), "{}", vf.text);
    assert!(vf.text.contains("VCons(embed_nat(Nat::add(gk, gk)), VNil)"), "{}", vf.text);

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

    // (c) the FIELDS control: swap the two field references of `pack`'s
    // constructor, so the IR builds `BSome(Succ(k), k)` where every emitted
    // proof says `BSome(k, Succ(k))`. Well-formed, right tag, right arity —
    // it RENDERS and computes the wrong value, which is the strong shape of
    // control (docs/certgen-cert-expression-design.md §8 item 3) rather than
    // an early decline.
    let good = &ctx_get(&ctx, "pack").text;
    let m = good
        .replace("pack_gen", "packm1_gen")
        .replacen("LetCon(1, RCons(1, RCons(0, RNil))", "LetCon(1, RCons(0, RCons(1, RNil))", 1);
    assert!(m.contains("LetCon(1, RCons(0, RCons(1, RNil))"), "the mutation must apply");
    refuted(&mut e, &m, "swapped constructor fields");
}

fn ctx_get<'a>(ctx: &'a GenCtx, name: &str) -> &'a heather_elab::certgen::Emission {
    ctx.iter().find(|e| e.name == name).expect("emission present")
}
