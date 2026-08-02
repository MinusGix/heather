//! `lib/ir_v1.hthr` — FunctionIR v1, `simulate`, and the fuel interface —
//! under `scripts/test`.
//!
//! The library file is the deliverable of docs/ir-simulate-design.md §11
//! items 1–4 and 6. The release check went 107s → 13.6s (closed subtrees) →
//! ~2.4s (definitions, issues/simulate-conversion-cost.md) → **1.25s** (the
//! value domain, issues/nbe-conversion-round.md) → **27s** once the fuel
//! interface landed: `step_mono`'s IH-generalizing motive is ~18s of that on
//! its own, which is the measured cost of the manual explicit-motive route
//! (issues/ih-generalization.md) → **34s** with the ∃-form of the fuel
//! interface (`Converges`, `BindInv`, issues/surface-existential.md).
//!
//! That last step is worth reading as two numbers, not one. The `BindInv`
//! inversion record **retired three of `step_mono`'s four convoy motives**, and
//! against the same file with the convoys restored that is **38.5s → 33.7s,
//! −12.6%**. The net +6.2s is the *added surface* — two records and nine
//! theorems, `Converges`/`refines` in ∃-form and the certificate exported
//! through them — and not the rewrite.
//!
//! The split is kept, and now earns its keep twice over: the declarations are
//! ~1.1s of the 34s, so the first test is a fast gate on everything that is
//! *not* a proof, and the second is the whole acceptance.
//!
//! Then **~194s** once `Refines` became a *name* rather than a statement shape
//! spelled out six times (`docs/types-as-expressions.md`,
//! `issues/type-definitions.md`): release 35.96s → 32.90s, −8.5%. Naming a
//! shape is a saving, not a cost — the statement is elaborated once, and
//! conversion compares a δ-stuck head instead of what it unfolds to.
//!
//! Then **~203s** with `Compile` v1 (docs/compile-typeclass-design.md):
//! `CompileNat2`, the milestone `add_instance`, the second instance through
//! the loop body, and two coupling controls — +5s debug, +0.35s release
//! (34.1s), all of it repackaging landed theorems.
//!
//! Then **~56s** with the cross-IR refinement round
//! (`issues/cross-ir-refinement.md`): a recursive-`Apply` `add`, its
//! env-independent invariant, `eval_functional`, and `RefinesNat2` between the
//! two structurally unrelated IRs — release 32.9s → 40.4s. The added time is
//! new surface (one more fuel-indexed induction and three concrete fixtures),
//! not a slowdown of anything landed.
//!
//! Then release **51s → 70s** with the ∃-COMPOSITION KIT (certifying-
//! generator v2, docs/certifying-generator-design.md §8 item 1): `k_ret`
//! plus `ret_conv`/`letcon_conv`/`letcall_conv`/`letmatch_conv` after
//! `conv_functional`. Nearly all of the +19s is the two double-`j` lemmas
//! (~9s each) — the same term-size price `step_mono` pays, two interpreters
//! in scope under a rewritten scrutinee. Measured worth it: the kit is
//! proved once and every *generated* certificate is a cheap fold over it
//! (`crates/elab/tests/certgen.rs`).
//!
//! BUDGET. This binary is **~75 CPU-seconds** against `scripts/test`'s
//! 300-second `ulimit -t`, and nearly all of that is the one full-library
//! test. It was ~203s (after 9.2s, 165s, 194s) until 2026-08-01, when the
//! workspace `[profile.dev.package.*]` overrides landed: the kernel/elab/
//! syntax crates now build at `opt-level = 3` even for dev test runs
//! (debug-assertions stay on), which bought back the ~6x a debug-built
//! kernel was paying on this file's conversion work. The old discipline
//! still applies at the new scale — weigh any theorem whose motive forces a
//! case tree over `Ir`, and if the file grows another `step_mono` the answer
//! is to make the elaborator compute generalized motives
//! (`issues/ih-generalization.md`) rather than to raise the limit — but a
//! second full-library elaboration now fits again if a round truly needs
//! one.
//!
//! - the first elaborates every DECLARATION (datatypes, helpers, the
//!   interpreter, the continuation helpers, the add programs) and runs the
//!   negative controls the file cannot state about itself — a wrong simulate
//!   claim, a false `<=` witness under `fuel_monotone`, and a wrong-result
//!   `equiv` — at the cheapest possible depth;
//! - the second is the full acceptance, the file's own theorems.

use heather_elab::Elaborator;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");

/// Everything up to the first theorem. The library keeps every `fn` and
/// `inductive` ahead of its theorem section for exactly this reason, so this
/// is precisely the declarations.
fn decls() -> &'static str {
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    &LIB[..cut]
}

/// `refl` at a false equation dies in the kernel as `NotConvertible`; a
/// mis-typed proof argument dies as an elaboration error. Either way the
/// point of a negative control is that the claim does **not** land.
fn refuted(e: &mut Elaborator, src: &str, what: &str) {
    match e.elab_source(src) {
        Err(_) => {}
        Ok(()) => panic!("{what} elaborated, but it is false"),
    }
}

#[test]
fn declarations_check_and_wrong_claims_are_refuted() {
    let src = decls();
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src)
        .unwrap_or_else(|err| panic!("{}", err.render(src)));

    // 1. Zero fuel is OutOfFuel; claiming it produced a value must fail. One
    // eval unfolding, so the control costs seconds, not minutes.
    let wrong = "theorem wrong(): eval(0, PNil)(VNil, Ret(RNil)) = Out(VNil) { refl }";
    match e.elab_source(wrong) {
        Err(err) => {
            let msg = format!("{err}");
            assert!(msg.contains("NotConvertible"), "unexpected refutation: {msg}");
        }
        Ok(()) => panic!("a false simulate claim elaborated"),
    }

    // 2. `fuel_monotone`'s statement family, refuted at the hypothesis that
    // makes it monotone rather than arbitrary: `leb(5)(3) = True` is
    // `False = True`, so no `refl` supplies it. Without this control a
    // `fuel_monotone` whose order hypothesis was vacuous would look identical
    // from the outside.
    refuted(
        &mut e,
        "theorem bad_le(): leb(5)(3) = True { refl }",
        "5 <= 3",
    );

    // …and the shape one step down: monotonicity is not symmetric. Claiming
    // a *smaller* fuel still answers is exactly the converse, and it fails at
    // the one place it can be seen concretely — the add loop mid-flight.
    refuted(
        &mut e,
        "theorem bad_anti(): eval(4, add_prog())(VCons(embed_nat(2), VCons(embed_nat(3), VNil)), \
         add_body()) = Out(VCons(embed_nat(5), VNil)) { refl }",
        "the add IR answering below its bound",
    );

    // 3. A wrong-result `equiv`: the bound is right, the answer is not. The
    // scrutinee here is a *literal* pair, which is the cheap half of the
    // axis; the file's own `add_equiv` carries the neutral one (`a`, `b` are
    // open Nats) and this control's purpose is only to show that being off by
    // one is visible at all.
    refuted(
        &mut e,
        "theorem bad_equiv(): eval(add(2, 5), add_prog())(VCons(embed_nat(2), \
         VCons(embed_nat(3), VNil)), add_body()) = Out(VCons(embed_nat(6), VNil)) { refl }",
        "add(2, 3) = 6 through the IR",
    );
}

/// The full library, acceptance theorems included: the deep combined
/// theorems, `step_mono`'s whole case tree, `fuel_monotone` in both shapes,
/// `Converges`/`BindInv` and the ∃-form of the refinement chain, and the
/// ∀-arguments `equiv`. 34s release; the debug figure is in this file's header
/// and is the reason nothing else lives in this test binary.
///
/// The ∃-form's negative controls ride along **in this test** rather than in
/// one of their own, deliberately: each would otherwise re-elaborate the whole
/// library, and two full elaborations do not fit the 300-second rail. They are
/// the controls the library cannot state about itself —
/// `Converges(p, env, ir, vs)` is a *predicate*, and the standing risk of the
/// encoding (docs/surface-value-parameters.md §2) is that a mis-weakened value
/// parameter would silently make it a vacuous one.
#[test]
fn the_full_ir_library_checks() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(LIB)
        .unwrap_or_else(|err| panic!("{}", err.render(LIB)));

    // The *wrong* answer at the right program and the right witness: refused.
    // If the `vs` parameter were captured under the Σ binder rather than
    // substituted, this would be the same proposition as `add_converges`'s,
    // which the library just proved.
    refuted(
        &mut e,
        "theorem conv_wrong(): Converges(add_prog(), VCons(embed_nat(1), \
         VCons(embed_nat(1), VNil)), add_body(), VCons(embed_nat(3), VNil)) \
         { Converges(50, refl) }",
        "converging to 3 where the IR answers 2",
    );

    // …and no witness closes a starved bound, so the `n` field is doing work
    // rather than being ignored by the encoding.
    refuted(
        &mut e,
        "theorem conv_starved(): Converges(add_prog(), VCons(embed_nat(1), \
         VCons(embed_nat(1), VNil)), add_body(), VCons(embed_nat(2), VNil)) \
         { Converges(1, refl) }",
        "converging at fuel 1",
    );

    // `BindInv`'s `hr` field pins the scrutinee, so an inversion claimed at a
    // `Stuck` sub-region — which produced no `ws` at all — must not check.
    refuted(
        &mut e,
        "theorem inv_wrong(ev: Val -> Ir -> Res, env: Val, rest: Ir, vs: Val) \
         : BindInv(ev, env, rest, Stuck, vs) { BindInv(VNil, refl, refl) }",
        "an inversion of a Stuck sub-region",
    );

    // `Compile` v1 controls (docs/compile-typeclass-design.md §7 item 3).
    // A wrong-result SPEC: the instance's certificate is the real theorem, so
    // the failure is precisely the coupling — `cert`'s expected type carries
    // `bad_spec` and the delivered convergence is to `add(b, a)`.
    refuted(
        &mut e,
        "fn bad_spec(a: Nat) -> Nat -> Nat { λ (b: Nat) => add(a, a) }\n\
         fn bad_instance() -> CompileNat2(bad_spec) {\n\
             CompileNat2 { prog: add_chain(), entry: ir_call2(),\n\
                 cert: λ (a: Nat) => λ (b: Nat) => add_converges_through_calls(a, b) } }",
        "an instance for a spec the IR does not implement",
    );

    // …and a wrong IR under the right spec: the certificate is about
    // `ir_call2()`, so an instance claiming it for the loop body must fail —
    // `entry` is substituted into `cert`'s type, not decoration.
    refuted(
        &mut e,
        "fn bad_entry() -> CompileNat2(add_spec) {\n\
             CompileNat2 { prog: add_chain(), entry: ir_loop(),\n\
                 cert: λ (a: Nat) => λ (b: Nat) => add_converges_through_calls(a, b) } }",
        "an instance whose entry is not the IR the certificate is about",
    );
}
