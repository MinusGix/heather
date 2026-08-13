//! The certifying generator, v2 — acceptance per
//! docs/certifying-generator-design.md §§8–9, under `scripts/test`.
//!
//! Since `issues/retire-rust-transcriber.md` stage 2 (2026-08-12) there is
//! exactly ONE generator: `generate_in_language`. The Rust walker that served
//! as its byte-identity oracle is deleted, so what that comparison pinned is
//! carried by four covers — `lib/certgen_code.hthr`'s own `refl` theorems, the
//! positive fixtures below (a silent decline is a panic), the exactness
//! fixtures inside every emission (different-but-converging output is `Stuck`
//! at a concrete run), and the kernel judging the rest. Where a property had no
//! cover left, the expected text is pinned as a LITERAL here: the `IR_*`
//! constants are the emitted-layout interface, whose sole normative statement
//! is now `lib/certgen_code.hthr`'s four-conventions header plus the emitters
//! in `crates/elab/src/certgen.rs`.
//!
//! BUDGET. This binary holds ONE test — the transcriptions and the declines,
//! which need only the declarations prefix, `lib/certgen_code.hthr` and
//! `lib/certgen_cert.hthr`. The end-to-end emissions and their mutation
//! controls moved to `certgen_emissions.rs` on 2026-08-12 (the non-`Nat`
//! embeddings round), because `ulimit -t` is per *process* and the two
//! together no longer fit one 300-second rail: each pays a ~40 s elaboration
//! of `lib/certgen_code.hthr` on top of its own work, and the rest of that
//! test is a ~50 s support prelude plus five emissions.
//!
//! The fold that turns a transcription into a certificate is a library file
//! too now (`lib/certgen_cert.hthr`, docs/certgen-cert-expression-design.md):
//! elaborating it is ~1 s, but *running* it costs ~3.5 CPU-s per generated
//! function on top of the transcriber, which every generating test here pays.
//! Its perturbation control lives in `certgen_cert.rs` — a binary of its own,
//! for the stack reason below and for a `ulimit -t` rail of its own.
//!
//! STACK: checking one `match code` shell means checking 52 branch telescopes
//! against a library-inductive motive, and two elaborations of
//! `lib/certgen_code.hthr` in one test thread overflow the 8 MiB
//! `scripts/test` gives it. One copy of the file per test, therefore.
//!
//! And one *rail* per binary: `ulimit -t` is per process, so the
//! perturbed-library controls live in `certgen_controls.rs`, the certificate
//! fold's in `certgen_cert.rs`, the emissions in `certgen_emissions.rs`, and
//! the non-`Nat` acceptance in `certgen_nonnat.rs`. Every one of them was a
//! test of this binary once; the split is what
//! `issues/certgen-harness-cost.md` calls the free lever, and it is free
//! because each of them already builds its own elaborator anyway.

use heather_elab::certgen::{generate_in_language, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

mod support;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");
/// The library's one import (docs/modules-design.md §7). Elaborated whole,
/// which is why the arithmetic and order kit is no longer sliced out of
/// `LIB` item by item below — `import nat;` in the declarations prefix brings
/// all of it into scope.
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
/// The transcriber: the data and helpers, plus the two `match code` shells
/// claiming `certgen.transcribe` and `certgen.check_sig`
/// (docs/certgen-transcriber-in-language-design.md,
/// docs/fn-signature-reflection-design.md). This file IS the fragment's
/// definition — signature rule and body rule both — and nothing in Rust
/// decides it.
const CODE: &str = include_str!("../../../lib/certgen_code.hthr");
/// The certificate fold: the `Cert`/`CertOut` data and the `fn`s that fold an
/// `Ir` into a chain of ∃-kit applications
/// (docs/certgen-cert-expression-design.md). Ordinary program-layer code — no
/// `match code`, so no 52-branch gate — and the emitters read its answer back
/// instead of deciding the fold in Rust.
const CERT: &str = include_str!("../../../lib/certgen_cert.hthr");

/// One library item's source text, by name — the same span slice `support`
/// uses, for the tests that need a single declaration rather than the prelude.
fn lib_item(name: &str) -> String {
    let file = parse_file(LIB).expect("the library parses");
    let span = file
        .items
        .iter()
        .find_map(|i| match i {
            Item::Inductive(ind) if ind.name == name => Some(ind.span),
            Item::Decl(d) if d.name == name => Some(d.span),
            _ => None,
        })
        .unwrap_or_else(|| panic!("the library declares {name}"));
    LIB[span.start..span.end].to_string()
}

/// A parsed `fn` declaration from the library — or from `nat`, where `add`
/// lives now — by name.
fn lib_decl(name: &str) -> Decl {
    let file = parse_file(LIB).expect("the library parses");
    let file = if file.items.iter().any(|i| matches!(i, Item::Decl(d) if d.name == name)) {
        file
    } else {
        parse_file(NAT).expect("`nat` parses")
    };
    file.items
        .into_iter()
        .find_map(|i| match i {
            Item::Decl(d) if d.name == name => Some(d),
            _ => None,
        })
        .unwrap_or_else(|| panic!("the library declares fn {name}"))
}

fn decl_of(src: &str) -> Decl {
    let file = parse_file(src).unwrap_or_else(|e| panic!("test fn parses: {e:?}"));
    assert_eq!(file.items.len(), 1);
    file.items.into_iter().next().unwrap().into_decl()
}

/// Test functions with no hand-written certificate anywhere.
const SEVEN: &str = "fn seven(n: Nat) -> Nat { 7 }";
const THIRD3: &str =
    "fn third3(a: Nat, b: Nat, c: Nat) -> Nat { match c { Zero => b, Succ(k) => Succ(third3(a, b, k)) } }";
/// The v2 acceptance function: a foreign call whose argument is the
/// self-call's result. The zero arm spells `Zero` rather than `0` because the
/// walker is source-blind and derives `Zero` where the source said `0` (both
/// denote the same Nat) — spelling it this way keeps `mul`'s pins about the
/// cross-function call rather than about literal spelling.
const MUL: &str =
    "fn mul(a: Nat, b: Nat) -> Nat { match b { Zero => Zero, Succ(k) => add(a, mul(a, k)) } }";


// ---------------------------------------------------------------------------
// THE LAYOUT INTERFACE, pinned as literals.
//
// Until 2026-08-12 the emitted layout was pinned by agreement between two
// independent implementations (the Rust walker and the in-language one). With
// the oracle retired these literals ARE that pin: the instruction chain, the
// slot numbering, the arm split, and the closure's callee indices, per
// function. `lib/certgen_code.hthr`'s `add_transcribes`, `dbl_transcribes` and
// `mul_transcribes` pin the same three transcriptions *in-language* — before
// the readback and before the closure renumbering — so a divergence between a
// literal here and a theorem there is localized to the readback or to the
// emitters, which is the seam the oracle used to cover.

/// §9 item 2: `add`'s IR is the hand-run's transcription up to the recorded
/// slot-map divergence — the generator transcribes `add` itself, which recurses
/// on its SECOND parameter (LetMatch on slot 1, gather (1, 0)), where the
/// hand-run transcribed the swapped spec to match the theta loop's convention
/// (LetMatch on slot 0, gather (0, 2)).
const IR_ADD: &str = "\
add_gen_arm_zero() = Ret(RCons(0, RNil))
add_gen_arm_succ() = LetCall(0, RCons(1, RCons(0, RNil)), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))
add_gen_body() = LetMatch(1, Arm(add_gen_arm_zero(), Arm(add_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// 1-ary recursive, a `Succ` arm nesting two constructors around the ih.
const IR_DBL: &str = "\
dbl_gen_arm_zero() = LetCon(0, RNil, Ret(RCons(0, RNil)))
dbl_gen_arm_succ() = LetCall(0, RCons(0, RNil), LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil)))))
dbl_gen_body() = LetMatch(0, Arm(dbl_gen_arm_zero(), Arm(dbl_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// 3-ary, recursion on the LAST parameter: the `Zero` arm returns a parameter
/// that is not the scrutinee (slot 1), and the self-call gathers the two
/// unchanged parameters around the field.
const IR_THIRD3: &str = "\
third3_gen_arm_zero() = Ret(RCons(1, RNil))
third3_gen_arm_succ() = LetCall(0, RCons(1, RCons(2, RCons(0, RNil))), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))
third3_gen_body() = LetMatch(2, Arm(third3_gen_arm_zero(), Arm(third3_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// Non-recursive, a numeral-literal body: eight instructions, not a constant.
const IR_SEVEN: &str = "\
seven_gen_body() = LetCon(0, RNil, LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))))))))";

/// The cross-function acceptance: a two-member closure `[add, mul]`, so the
/// self-call renders `LetCall(1, …)` and the foreign call `LetCall(0, …)` —
/// the walker's own numbering (0 = self, foreign tags verbatim) renumbered
/// against the closure at readback, which is the one place the two numbering
/// systems meet.
const IR_MUL: &str = "\
mul_gen_arm_zero() = LetCon(0, RNil, Ret(RCons(0, RNil)))
mul_gen_arm_succ() = LetCall(1, RCons(1, RCons(0, RNil)), LetCall(0, RCons(2, RCons(0, RNil)), Ret(RCons(0, RNil))))
mul_gen_body() = LetMatch(1, Arm(mul_gen_arm_zero(), Arm(mul_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))";

/// Everything here elaborates **as the library module**, so that the
/// declarations prefix's `import nat;` means what it means in the file.
fn elab(e: &mut Elaborator, src: &str, what: &str) {
    e.elab_module_source("ir_v1", src)
        .unwrap_or_else(|err| panic!("{what}:\n{}", err.render(src)));
}

fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    if e.elab_module_source("ir_v1", src).is_ok() {
        panic!("{what} elaborated, but it must fail");
    }
}

/// A prelude'd elaborator with `nat` in it — the closure `heather check
/// lib/ir_v1.hthr` walks, minus the root.
fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("bool", BOOL).unwrap_or_else(|err| panic!("{}", err.render(BOOL)));
    e.elab_module_source("nat", NAT).unwrap_or_else(|err| panic!("{}", err.render(NAT)));
    e
}

/// The transcriber's own acceptance: what each fixture transcribes to, and
/// what the fragment declines. Cheap on purpose — the *declarations* prefix is
/// all this needs, not the support prelude, because nothing here elaborates a
/// certificate. The end-to-end emissions and the kernel-refusal controls live
/// in `emissions_check_and_controls`, which already pays for the kit.
#[test]
fn in_language_transcriber() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    // The checked-in prefix goes through the shared declaration cache
    // (`support::with_decl_cache`'s header owns the argument); everything
    // after the closing brace faces the kernel unconditionally.
    support::with_decl_cache(&mut e, |e| {
        elab(e, &LIB[..cut], "declarations prefix");
        elab(e, CODE, "lib/certgen_code.hthr");
        elab(e, CERT, "lib/certgen_cert.hthr");
    });
    // `dbl` lives past the declarations cut, and the generator reads the
    // *elaborated* body: a fn the elaborator has not seen has nothing to
    // analyse, which is a decline, not a bug.
    elab(&mut e, &lib_item("dbl"), "fn dbl");
    elab(&mut e, SEVEN, "fn seven");
    elab(&mut e, THIRD3, "fn third3");
    elab(&mut e, MUL, "fn mul");

    // The single-function positives, across the axes of
    // docs/testing-generated-terms.md: recursion on the second parameter
    // (`add`), on the only parameter (`dbl`), on the last of three (`third3`),
    // and no recursion at all over a literal body (`seven`).
    for (d, want) in [
        (lib_decl("add"), IR_ADD),
        (lib_decl("dbl"), IR_DBL),
        (decl_of(THIRD3), IR_THIRD3),
        (decl_of(SEVEN), IR_SEVEN),
    ] {
        let em = generate_in_language(&e, &d, &GenCtx::new())
            .unwrap_or_else(|r| panic!("{} declined: {r}", d.name));
        assert_eq!(em.ir_body, want, "{} transcribes differently", d.name);
        assert_eq!(em.closure, vec![d.name.clone()], "{}'s closure", d.name);
    }
    assert_eq!(
        generate_in_language(&e, &lib_decl("add"), &GenCtx::new()).unwrap().arity,
        2
    );
    // The hand-run's own slot map, for the divergence `IR_ADD` records.
    assert!(LIB.contains("LetCall(0, RCons(0, RCons(2, RNil)),"));

    // The cross-function positive (docs/opaque-globals-analysis-design.md §4):
    // `mul` calls `add`, whose head arrives as a callee marker through the
    // body-reflection primitive, and with `add`'s emission in the context the
    // closure is the two-member program.
    let mul = decl_of(MUL);
    let mut cross = GenCtx::new();
    cross.push(generate_in_language(&e, &lib_decl("add"), &GenCtx::new()).expect("add"));
    let em = generate_in_language(&e, &mul, &cross)
        .unwrap_or_else(|r| panic!("mul declined: {r}"));
    assert_eq!(em.ir_body, IR_MUL, "mul transcribes differently");
    assert_eq!(em.closure, vec!["add".to_string(), "mul".to_string()]);

    // With NO generated instance for the callee in the context, the walk and
    // readback still succeed and the decline is the closure's, downstream —
    // the only home left for "a call to a function that has no certificate
    // yet" now that the surface fragment check is gone.
    let Err(msg) = generate_in_language(&e, &mul, &GenCtx::new()) else {
        panic!("mul without add's instance must decline")
    };
    assert!(msg.contains("no generated instance"), "{msg}");

    // The body-less policy pin (docs/opaque-globals-analysis-design.md §2): a
    // theorem's proof is deliberately opaque, so body reflection declines by
    // saying so. The name is one of `lib/certgen_code.hthr`'s own theorems,
    // elaborated above.
    let Err(msg) = e.fn_body_code("sig_dbl") else {
        panic!("a theorem has no body to reflect")
    };
    assert!(msg.contains("no elaborated body"), "{msg}");

    // A body decline, from the WALKER: a nested `match` binds at level
    // `arity + 2`, which convention 1 says is outside the fragment
    // (`lib/certgen_code.hthr`'s `nested_binder_declines` pins the same fact
    // one layer down).
    {
        let src = "fn nest2(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => match k { Zero => 1, Succ(j) => j } } }";
        let d = decl_of(src);
        elab(&mut e, src, "body decline fixture");
        let Err(msg) = generate_in_language(&e, &d, &GenCtx::new()) else {
            panic!("`{}` must decline", d.name)
        };
        assert!(msg.contains("declined this body"), "{msg}");
    }

    // The in-language signature checker
    // (docs/fn-signature-reflection-design.md §§4, 7.5): a non-`Nat`
    // parameter, a non-`Nat` result and a nullary fn are each declined by the
    // LIBRARY's `check_sig` — the message says so — and none is a
    // disagreement with the Rust peel, which is the agreement property
    // asserted from the negative side. (The positives above assert it from
    // the accepting side: a disagreement is an `Err`, and they demand `Ok`.)
    //
    // ONE FLIP, recorded rather than hidden
    // (docs/certgen-non-nat-embeddings-design.md §9 item 7): this list used to
    // contain `fn tocmp(n: Nat) -> Cmp { CLt }` as a "non-`Nat` result"
    // decline. A three-constructor tier-0 enumeration is now IN the fragment,
    // so that fixture became a positive and is replaced by two declines this
    // round still makes: a TIER-1 (recursive) result type, whose `Wf` lowering no
    // arm of the shell is written for. (The non-`Nat` positives, and the
    // decline for a constructor with a non-`Nat` field, live in
    // `crates/elab/tests/certgen_nonnat.rs` — its own binary, for its own
    // `ulimit -t`, which is the free lever `issues/certgen-harness-cost.md`
    // records.)
    for src in [
        "fn evalish2(v: Val) -> Nat { 0 }",
        "fn torefs(n: Nat) -> Refs { RNil }",
        "fn nofn() -> Nat { 0 }",
    ] {
        let d = decl_of(src);
        elab(&mut e, src, "signature decline fixture");
        let Err(msg) = generate_in_language(&e, &d, &GenCtx::new()) else {
            panic!("`{}`'s signature must decline", d.name)
        };
        assert!(msg.contains("in-language signature checker"), "{msg}");
        assert!(!msg.contains("disagreement"), "{msg}");
    }

    // Two declines the retired Rust walker used to make, re-homed
    // (issues/retire-rust-transcriber.md stage 2). A non-structural self-call
    // never reaches the generator at all: the ELABORATOR refuses it, because
    // the only recursion it lowers is the eliminator's.
    refuted(
        &mut e,
        "fn tw(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => tw(k, k) } }",
        "a non-structural self-call",
    );
    // And a `Succ` arm without a self-call is now IN the fragment — a
    // widening, not a loss. The Rust walker declined it as a surface shape;
    // the eliminator carries structural recursion, so an arm that ignores the
    // induction hypothesis is an ordinary transcribable body.
    {
        let src = "fn pred2(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => k } }";
        elab(&mut e, src, "pred2");
        let em = generate_in_language(&e, &decl_of(src), &GenCtx::new())
            .expect("a Succ arm without a self-call is transcribable");
        assert!(em.ir_body.contains("pred2_gen_arm_succ() = Ret(RCons(0, RNil))"), "{}", em.ir_body);
    }
}

