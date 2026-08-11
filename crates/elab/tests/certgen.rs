//! The certifying generator, v2 — acceptance per
//! docs/certifying-generator-design.md §§8–9, under `scripts/test`.
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
//! against a fresh prelude, and the forced control reuses the same session.

use heather_elab::certgen::{
    compile_record, generate, generate_forced, generate_in_language, GenCtx,
};
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
/// The in-language transcriber: the data and helpers, plus the `match code`
/// shell that claims `certgen.transcribe`
/// (docs/certgen-transcriber-in-language-design.md).
const CODE: &str = include_str!("../../../lib/certgen_code.hthr");

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
/// self-call's result.
const MUL: &str =
    "fn mul(a: Nat, b: Nat) -> Nat { match b { Zero => 0, Succ(k) => add(a, mul(a, k)) } }";

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

/// §9 item 2: the generated `add` IR is the hand-run's transcription, up to
/// the recorded slot-map divergence (the generator transcribes `add`
/// itself, which recurses on its SECOND parameter — LetMatch on slot 1,
/// gather (1, 0) — where the hand-run transcribed the swapped spec to match
/// the theta loop's convention: LetMatch on slot 0, gather (0, 2)).
#[test]
fn generated_add_matches_the_hand_run() {
    let em = generate(&lib_decl("add"), &GenCtx::new()).expect("add is in the fragment");
    assert_eq!(em.arity, 2);
    assert_eq!(em.closure, vec!["add".to_string()]);
    assert_eq!(
        em.ir_body,
        "add_gen_arm_zero() = Ret(RCons(0, RNil))\n\
         add_gen_arm_succ() = LetCall(0, RCons(1, RCons(0, RNil)), LetCon(1, RCons(0, RNil), Ret(RCons(0, RNil))))\n\
         add_gen_body() = LetMatch(1, Arm(add_gen_arm_zero(), Arm(add_gen_arm_succ(), NoArm)), Ret(RCons(0, RNil)))"
    );
    assert!(LIB.contains("LetCall(0, RCons(0, RCons(2, RNil)),"));
}

/// One elaborator serves the whole acceptance: the support prelude is the
/// expensive part (the ∃-kit and its `step_mono`/`fuel_monotone` chain
/// re-elaborate), so the positive emissions, the mutation controls (renamed
/// apart) and the forced-emission control all share it.
///
/// Positives:
/// - `add` (the hand-run reproduction), `dbl` (1-ary recursive), `seven`
///   (non-recursive), `third3` (3-ary recursive) — §9 item 3;
/// - `mul` via `add` — the v2 cross-function acceptance: a two-function
///   program, `add`'s invariant re-derived inside it, the caller's
///   certificate consuming the callee's at an open argument.
#[test]
fn emissions_check_and_controls() {
    let mut e = base();
    let sup = support();
    elab(&mut e, &sup, "support prelude");
    elab(&mut e, SEVEN, "fn seven");
    elab(&mut e, THIRD3, "fn third3");
    elab(&mut e, MUL, "fn mul");

    let mut ctx = GenCtx::new();
    let mut arities_done = vec![2usize];
    for d in [lib_decl("add"), lib_decl("dbl"), decl_of(SEVEN), decl_of(THIRD3), decl_of(MUL)] {
        let em = generate(&d, &ctx).unwrap_or_else(|r| panic!("{} declined: {r}", d.name));
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

    // The in-language path's own end-to-end item (design doc §10.4): `seven`
    // is the one fixture whose in-language emission is a *different file* from
    // the Rust one — its body is a numeral literal, so the walker spells the
    // spec `Succ(…)` where the source said `7` — and it is checked here
    // because this is the test that pays for the kit.
    let mut il = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    elab(&mut il, &LIB[..cut], "declarations prefix");
    elab(&mut il, CODE, "lib/certgen_code.hthr");
    elab(&mut il, SEVEN, "fn seven");
    elab(&mut il, &lib_item("dbl"), "fn dbl");
    let em = generate_in_language(&il, &decl_of(SEVEN), &GenCtx::new())
        .unwrap_or_else(|r| panic!("seven declined in-language: {r}"));
    elab(&mut e, &em.text.replace("seven_gen", "sevenil_gen"), "in-language seven emission");

    // Fragment honesty, the forced half: `tri` calls `dbl`, unknown to an
    // empty context, so the forced transcription routes it to the self-call
    // — a different function — and the invariant's final `refl` faces
    // `dbl(gk) ≡ tri(gk)` at an open `gk`, which is not convertible.
    let tri = "fn tri(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(dbl(k)) } }";
    let d = decl_of(tri);
    assert!(generate(&d, &GenCtx::new()).is_err(), "tri is outside the fragment");
    let em = generate_forced(&d, &GenCtx::new()).expect("forced emission");
    elab(&mut e, tri, "fn tri");
    refuted(&mut e, &em.text, "forced out-of-fragment emission");
}

/// The in-language transcriber (docs/certgen-transcriber-in-language-design.md
/// §10): `lib/certgen_code.hthr` plus the `match code` shell replace the Rust
/// `Compiler` for one phase, and the cross-check is that they transcribe the
/// same program.
///
/// Cheap on purpose — the *declarations* prefix is all this needs, not the
/// support prelude, because nothing here elaborates a certificate. The
/// end-to-end emission check and the forced control live in
/// `emissions_check_and_controls`, which already pays for the kit.
#[test]
fn in_language_transcriber() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    elab(&mut e, &LIB[..cut], "declarations prefix");
    elab(&mut e, CODE, "lib/certgen_code.hthr");
    // `dbl` lives past the declarations cut, and the in-language path reads the
    // *elaborated* body: a fn the elaborator has not seen has nothing to
    // analyse, which is a decline, not a bug.
    elab(&mut e, &lib_item("dbl"), "fn dbl");
    elab(&mut e, SEVEN, "fn seven");
    elab(&mut e, THIRD3, "fn third3");
    elab(&mut e, MUL, "fn mul");

    // The cross-check: same IR, function by function. Where the source has no
    // numeral literal the whole *emission* matches too — the model is all the
    // emitters see, so an equal IR plus equal parameter names is an equal
    // file, which is a sharper statement than conversion and a cheaper one.
    for d in [lib_decl("add"), lib_decl("dbl"), decl_of(THIRD3)] {
        let rust = generate(&d, &GenCtx::new()).unwrap_or_else(|r| panic!("{r}"));
        let inlang = generate_in_language(&e, &d, &GenCtx::new())
            .unwrap_or_else(|r| panic!("{} declined in-language: {r}", d.name));
        assert_eq!(inlang.ir_body, rust.ir_body, "{} transcribes differently", d.name);
        assert_eq!(inlang.text, rust.text, "{}'s emission differs", d.name);
    }

    // `seven`'s body is a numeral literal, so the two paths agree on the IR
    // and differ on the *spec spelling* only: the source says `7`, and a
    // walker that never saw the source says `Succ(…)`. Both denote the same
    // Nat, and the emission is checked in the expensive test.
    let d = decl_of(SEVEN);
    let rust = generate(&d, &GenCtx::new()).expect("seven");
    let inlang = generate_in_language(&e, &d, &GenCtx::new()).expect("seven, in-language");
    assert_eq!(inlang.ir_body, rust.ir_body);
    assert_ne!(inlang.text, rust.text);

    // Declines. The first is the fragment boundary the *kernel* draws: `mul`
    // calls `add`, and `elim^Trm` is neutral on `box (u^δ)`, so the walk stops
    // at the global — while the Rust v2 path generates it happily, which is
    // what makes this the in-language path's decline and not the generator's.
    let mul = decl_of(MUL);
    let Err(msg) = generate_in_language(&e, &mul, &GenCtx::new()) else {
        panic!("a cross-function call is outside the in-language fragment")
    };
    assert!(msg.contains("global"), "{msg}");
    assert!(generate(&mul, &{
        let mut c = GenCtx::new();
        c.push(generate(&lib_decl("add"), &GenCtx::new()).expect("add"));
        c
    })
    .is_ok());

    // A body the marker pass cannot close: a `let` is not in the fragment.
    // (The signature is fine, so this decline is the *body* residue's, after
    // the in-language signature verdict said yes.)
    {
        let src = "fn withlet2(n: Nat) -> Nat { let m = n; m }";
        let d = decl_of(src);
        elab(&mut e, src, "decline fixture");
        let Err(msg) = generate_in_language(&e, &d, &GenCtx::new()) else {
            panic!("`{}` must decline in-language", d.name)
        };
        assert!(msg.contains("let"), "{msg}");
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
            panic!("`{}`'s signature must decline in-language", d.name)
        };
        assert!(msg.contains("in-language signature checker"), "{msg}");
        assert!(!msg.contains("disagreement"), "{msg}");
    }
}

/// The in-language honesty control (design doc §10.6a), in a test of its own
/// **because of the stack**: checking one `match code` shell means checking 52
/// branch telescopes against a library-inductive motive, and two of those in
/// one test thread overflow the 8 MiB `scripts/test` gives it. One shell per
/// thread is also the cheaper arrangement.
#[test]
fn a_perturbed_transcriber_is_refused_by_the_kernel() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    elab(&mut e, &LIB[..cut], "declarations prefix");
    // The honesty control, and the whole architecture in one edit: perturb the
    // *library* — `ta_succ` emitting the `Zero` tag — and what it produces
    // must fail to check rather than prove anything about `dbl`.
    //
    // It arrives as two controls, because the file states its own acceptance:
    // the perturbed `dist` is refused by `certgen_code.hthr`'s own theorems
    // before anything downstream sees it. Strip those, and the emission is the
    // only thing on trial — its *exactness fixture*, which needs nothing but
    // the declarations prefix, so this control costs no kit.
    let bad_code = CODE.replace(
        "TExp(PCon(1, QCons(res, QNil), pre), RLoc(len), Succ(len))",
        "TExp(PCon(0, QCons(res, QNil), pre), RLoc(len), Succ(len))",
    );
    assert_ne!(bad_code, CODE, "the mutation must apply");
    if e.elab_module_source("ir_v1", &bad_code).is_ok() {
        panic!("the library's own theorems must refuse a perturbed `dist`");
    }
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    let shell = bad_code.find("// The shell").expect("the shell is the file's last block");
    let stripped = format!("{}\n{}", &bad_code[..thms], &bad_code[shell..]);
    // The failed elaboration above stopped at a theorem, which is *before* the
    // file's shell, so this is still the only 52-branch check in this thread.
    let mut bad = base();
    elab(&mut bad, &LIB[..cut], "declarations prefix");
    elab(&mut bad, &stripped, "mutated lib/certgen_code.hthr");
    elab(&mut bad, &lib_item("dbl"), "fn dbl");
    let wrong = generate_in_language(&bad, &lib_decl("dbl"), &GenCtx::new())
        .expect("a wrong transcriber still emits — that is the point");
    let good = generate(&lib_decl("dbl"), &GenCtx::new()).expect("dbl");
    assert_ne!(wrong.ir_body, good.ir_body, "the mutation must change the transcription");
    // Everything up to the invariant: the IR, the program, and the two
    // literal-fuel fixtures. The fixtures are `refl` on a concrete run, so a
    // transcription that reads the wrong slots is `Stuck` there.
    let upto = wrong.text.find("theorem dbl_gen_conv").expect("the emission proves an invariant");
    refuted(&mut bad, &wrong.text[..upto], "mutated-transcriber emission");
}

/// The agreement property's loud half (docs/fn-signature-reflection-design.md
/// §4): perturb the LIBRARY's signature rule — `sig_finish` accepting the
/// nullary signature — and a nullary fn's generation must fail with the
/// **disagreement** message, never silently ride either verdict. Own test for
/// the same stack reason as above (a second `match code` shell check per
/// thread), and with the file's own theorems stripped first, because they
/// refuse the mutation before anything downstream sees it — the same
/// two-controls shape as the transcriber's honesty control.
#[test]
fn a_perturbed_signature_checker_is_a_loud_disagreement() {
    let mut e = base();
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    elab(&mut e, &LIB[..cut], "declarations prefix");
    let bad_code = CODE.replace(
        "SigYes(a) => match a { Zero => SigNo, Succ(k) => SigYes(Succ(k)) },",
        "SigYes(a) => SigYes(a),",
    );
    assert_ne!(bad_code, CODE, "the mutation must apply");
    if e.elab_module_source("ir_v1", &bad_code).is_ok() {
        panic!("the library's own theorems must refuse a perturbed `sig_finish`");
    }
    let thms = bad_code.find("\ntheorem ").expect("the file states its own acceptance");
    let shell = bad_code.find("// The shell").expect("the shells are the file's last block");
    let stripped = format!("{}\n{}", &bad_code[..thms], &bad_code[shell..]);
    // The failed elaboration stopped at a theorem, before either shell, so the
    // stripped file's two shells are this thread's only 52-branch checks.
    let mut bad = base();
    elab(&mut bad, &LIB[..cut], "declarations prefix");
    elab(&mut bad, &stripped, "mutated lib/certgen_code.hthr");
    let nofn = "fn nofn2() -> Nat { 0 }";
    elab(&mut bad, nofn, "fn nofn2");
    let Err(msg) = generate_in_language(&bad, &decl_of(nofn), &GenCtx::new()) else {
        panic!("a nullary fn must not generate")
    };
    assert!(msg.contains("disagreement"), "{msg}");
}

fn ctx_get<'a>(ctx: &'a GenCtx, name: &str) -> &'a heather_elab::certgen::Emission {
    ctx.iter().find(|e| e.name == name).expect("emission present")
}

/// Fragment honesty, the decline half — pure Rust, no elaborator.
#[test]
fn fragment_declines() {
    let empty = GenCtx::new();
    let declined = [
        // call to a function with no generated instance in the context
        "fn dblv(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(dbl(k))) } }",
        // non-Nat parameter
        "fn evalish(v: Val) -> Nat { 0 }",
        // let statement
        "fn withlet(n: Nat) -> Nat { let m = n; m }",
        // Succ arm without a self-call
        "fn pred2(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => k } }",
        // non-structural self-call argument
        "fn tw(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => tw(k, k) } }",
    ];
    for src in declined {
        let d = decl_of(src);
        assert!(generate(&d, &empty).is_err(), "`{}` must be declined", d.name);
    }
}
