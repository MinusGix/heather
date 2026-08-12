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
//! is now `lib/certgen_code.hthr`'s three-conventions header plus the emitters
//! in `crates/elab/src/certgen.rs`.
//!
//! Support prelude: the library's declarations section (everything up to
//! the first theorem, the same cut `ir_v1.rs` uses) plus the named items a
//! generated emission's *proofs* elaborate against, sliced by parse span in
//! dependency order: the ∃-composition kit (`ret_conv`…`letmatch_conv`) and
//! its chain (`BindInv` → `step_mono` → `fuel_monotone`, the `le` kit),
//! `Converges`, `CompileNat2`, and `dbl`. Generated code references only
//! these — never the library's IR theorems — so the harness never pays the
//! full-file elaboration.
//!
//! BUDGET: measured 2026-08-02 (dev profile with the workspace opt-level
//! overrides): ~108 CPU-seconds for this binary against `scripts/test`'s
//! 300-second per-process rail — **160s** re-measured late 2026-08-05
//! (issues/suite-wall-time-two-tests.md; past certgen-harness-cost's 200s
//! trigger-watch zone at 53% of the rail — the snapshot/CLI levers there
//! are next when it crosses). `scripts/test --fast` skips
//! `emissions_check_and_controls` by name for the inner loop; a round's
//! final verification runs it. **~128s** earlier 2026-08-05, when the
//! arithmetic and order kit moved to `lib/std/nat.hthr`
//! (docs/modules-design.md §7) and the support prelude started elaborating
//! that module *whole* instead of slicing nine items out of it. The split is
//! roughly: ~50s the support prelude (dominated by re-elaborating
//! `step_mono` and the two double-`j` kit lemmas), ~50s the five emissions,
//! the rest the controls. That is why there is exactly ONE elaborator: the
//! prelude is paid once, mutants are renamed apart rather than re-elaborated
//! against a fresh prelude, and `lib/certgen_code.hthr` — whose two `match
//! code` shells are the expensive part of any generation — is elaborated into
//! that same session, once.
//!
//! The fold that turns a transcription into a certificate is a library file
//! too now (`lib/certgen_cert.hthr`, docs/certgen-cert-expression-design.md):
//! elaborating it is ~1 s, but *running* it costs ~3.5 CPU-s per generated
//! function on top of the transcriber, which is what this binary's two
//! generating tests pay. Its perturbation control lives in
//! `certgen_cert.rs` — a binary of its own, for the stack reason below and
//! for a `ulimit -t` rail of its own.
//!
//! STACK: checking one `match code` shell means checking 52 branch telescopes
//! against a library-inductive motive, and two elaborations of
//! `lib/certgen_code.hthr` in one test thread overflow the 8 MiB
//! `scripts/test` gives it. One copy of the file per test, therefore.
//!
//! And one *rail* per binary: `ulimit -t` is per process, so the
//! perturbed-library controls live in `certgen_controls.rs` and the
//! certificate fold's in `certgen_cert.rs`. They were tests of this binary
//! until the fold's evaluation cost pushed the four of them past the
//! 300-second rail (2026-08-12) — the split is what
//! `issues/certgen-harness-cost.md` calls the free lever, and it is free
//! because each control already builds its own elaborator anyway.

use heather_elab::certgen::{compile_record, generate_in_language, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

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

/// Items a generated emission needs beyond the declarations prefix, in
/// dependency (file-consistent) order.
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
    elab(&mut e, &LIB[..cut], "declarations prefix");
    elab(&mut e, CODE, "lib/certgen_code.hthr");
    elab(&mut e, CERT, "lib/certgen_cert.hthr");
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
    for src in [
        "fn evalish2(v: Val) -> Nat { 0 }",
        "fn tocmp(n: Nat) -> Cmp { CLt }",
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

/// One elaborator serves the whole acceptance: the support prelude and
/// `lib/certgen_code.hthr` are the expensive parts, so the positive emissions
/// and the mutation controls (renamed apart) all share it.
///
/// Positives — every one of them generated, elaborated and kernel-checked:
/// - `add` (the hand-run reproduction), `dbl` (1-ary recursive), `seven`
///   (non-recursive), `third3` (3-ary recursive) — §9 item 3;
/// - `mul` via `add` — the v2 cross-function acceptance: a two-function
///   program, `add`'s invariant re-derived inside it, the caller's
///   certificate consuming the callee's at an open argument.
///
/// This is cover (b) of `issues/retire-rust-transcriber.md`: with no oracle
/// left, a transcriber that silently started declining would show up here as a
/// panic, and one that emitted a different-but-plausible program would be
/// refused by its own exactness fixture or by the kernel.
#[test]
fn emissions_check_and_controls() {
    let mut e = base();
    let sup = support();
    elab(&mut e, &sup, "support prelude");
    elab(&mut e, CODE, "lib/certgen_code.hthr");
    elab(&mut e, CERT, "lib/certgen_cert.hthr");
    elab(&mut e, SEVEN, "fn seven");
    elab(&mut e, THIRD3, "fn third3");
    elab(&mut e, MUL, "fn mul");

    let mut ctx = GenCtx::new();
    let mut arities_done = vec![2usize];
    for d in [lib_decl("add"), lib_decl("dbl"), decl_of(SEVEN), decl_of(THIRD3), decl_of(MUL)] {
        let em = generate_in_language(&e, &d, &ctx)
            .unwrap_or_else(|r| panic!("{} declined: {r}", d.name));
        if !arities_done.contains(&em.arity) {
            let rec = compile_record(em.arity).expect("non-2 arity record");
            elab(&mut e, &rec, "arity record");
            arities_done.push(em.arity);
        }
        elab(&mut e, &em.text, &format!("emission for {}", em.name));
        ctx.push(em);
    }

    // The mul emission really is the two-function program with the
    // re-derived callee invariant.
    let mul = ctx_get(&ctx, "mul");
    assert_eq!(mul.closure, vec!["add".to_string(), "mul".to_string()]);
    assert!(mul.text.contains("add_gen_conv_in_mul"));

    // §9 item 4, the mutation controls: perturb the known-good dbl emission
    // and the certificate refuses. Renamed apart so one elaborator serves
    // all of them (dbl's emission itself is already elaborated above).
    let good = &ctx_get(&ctx, "dbl").text;
    let rename = |s: &str, tag: &str| s.replace("dbl_gen", &format!("dbl{tag}_gen"));

    // (a) a reference off by one in the IR: the emitted proofs still spell
    // the correct chain, so the invariant no longer matches the body.
    let m = rename(good, "m1").replacen("LetCall(0, RCons(0, RNil)", "LetCall(0, RCons(3, RNil)", 1);
    assert_ne!(m, rename(good, "m1"));
    refuted(&mut e, &m, "off-by-one reference");

    // (b) a wrong-result fixture claim: the spec argument perturbed.
    let m = rename(good, "m2").replacen("embed_nat(dbl(2))", "embed_nat(dbl(3))", 1);
    assert_ne!(m, rename(good, "m2"));
    refuted(&mut e, &m, "wrong fixture result");

    // (c) the wrong constructor tag in the IR.
    let m = rename(good, "m3").replacen("LetCon(1, RCons(0, RNil)", "LetCon(0, RCons(0, RNil)", 1);
    assert_ne!(m, rename(good, "m3"));
    refuted(&mut e, &m, "wrong constructor tag");

    // (d) the instance claims a different spec function of the same arity.
    let m = rename(good, "m4").replacen("CompileNat1(dbl)", "CompileNat1(seven)", 1);
    assert_ne!(m, rename(good, "m4"));
    refuted(&mut e, &m, "wrong spec function");

    // (e) CALLEE IDENTITY, the control the retired `generate_forced` used to
    // play (issues/retire-rust-transcriber.md stage 2): a `LetCall` names a
    // slot in the program, so swapping the program's two members routes every
    // call to the other function while the whole emission stays well-formed.
    // `mul`'s self-call becomes an `add` call and vice versa, the run stops
    // converging, and the exactness fixture — a `refl` on a concrete run —
    // refuses it. Cheaper than the old control and cross-function, which the
    // old one was not.
    let mutant = ctx_get(&ctx, "mul")
        .text
        .replace("mul_gen", "mulm5_gen")
        .replace("_in_mul", "_in_mulm5")
        .replacen(
            "PFun(add_gen_body(), PFun(mulm5_gen_body(), PNil))",
            "PFun(mulm5_gen_body(), PFun(add_gen_body(), PNil))",
            1,
        );
    assert!(
        mutant.contains("PFun(mulm5_gen_body(), PFun(add_gen_body(), PNil))"),
        "the mutation must apply"
    );
    refuted(&mut e, &mutant, "a program whose members are swapped");
}

fn ctx_get<'a>(ctx: &'a GenCtx, name: &str) -> &'a heather_elab::certgen::Emission {
    ctx.iter().find(|e| e.name == name).expect("emission present")
}
