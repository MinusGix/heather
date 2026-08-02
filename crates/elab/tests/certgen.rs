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
//! 300-second per-process rail. The split is roughly: ~50s the support
//! prelude (dominated by re-elaborating `step_mono` and the two double-`j`
//! kit lemmas), ~50s the five emissions, the rest the controls. That is
//! why there is exactly ONE elaborator: the prelude is paid once, mutants
//! are renamed apart rather than re-elaborated against a fresh prelude,
//! and the forced control reuses the same session.

use heather_elab::certgen::{compile_record, generate, generate_forced, GenCtx};
use heather_elab::Elaborator;
use heather_syntax::ast::{Decl, Item};
use heather_syntax::parse_file;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");

/// Items a generated emission needs beyond the declarations prefix, in
/// dependency (file-consistent) order.
const SUPPORT_ITEMS: [&str; 23] = [
    "dbl",
    "BindInv",
    "k_bind_inv",
    "k_bind_mono",
    "step_mono",
    "eval_mono_succ",
    "eval_mono_plus",
    "cong_nat",
    "add_left_zero",
    "add_succ_left",
    "sub_zero",
    "le_add",
    "le_refl",
    "le_succ_r",
    "le_add_l",
    "le_add_r",
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

/// A parsed `fn` declaration from the library by name.
fn lib_decl(name: &str) -> Decl {
    let file = parse_file(LIB).expect("the library parses");
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

fn elab(e: &mut Elaborator, src: &str, what: &str) {
    e.elab_source(src).unwrap_or_else(|err| panic!("{what}:\n{}", err.render(src)));
}

fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    if e.elab_source(src).is_ok() {
        panic!("{what} elaborated, but it must fail");
    }
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
    let mut e = Elaborator::with_prelude().expect("prelude");
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
