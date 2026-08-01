//! `lib/ir_v1.hthr` — FunctionIR v1, `simulate`, and the fuel interface —
//! under `scripts/test`.
//!
//! The library file is the deliverable of docs/ir-simulate-design.md §11
//! items 1–4 and 6. The release check went 107s → 13.6s (closed subtrees) →
//! ~2.4s (definitions, issues/simulate-conversion-cost.md) → **1.25s** (the
//! value domain, issues/nbe-conversion-round.md) → **27s** once the fuel
//! interface landed: `step_mono`'s IH-generalizing motive is ~18s of that on
//! its own, which is the measured cost of the manual explicit-motive route
//! (issues/ih-generalization.md).
//!
//! The split is kept, and now earns its keep twice over: the declarations are
//! 1.1s of the 27s, so the first test is a fast gate on everything that is
//! *not* a proof, and the second is the whole acceptance.
//!
//! BUDGET. This binary is **165 CPU-seconds** debug against `scripts/test`'s
//! 300-second `ulimit -t` (was 9.2s), and 155s of that is the one full-library
//! test. That is the headroom this file has left: the next theorem in
//! `lib/ir_v1.hthr` whose motive forces a case tree over `Ir` should be
//! weighed against it, and if the file grows another `step_mono` the answer is
//! to make the elaborator compute generalized motives
//! (`issues/ih-generalization.md`) rather than to raise the limit.
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
/// the refinement chain, and the ∀-arguments `equiv`. 27s release; the debug
/// figure is in this file's header and is the reason nothing else lives in
/// this test binary.
#[test]
fn the_full_ir_library_checks() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(LIB)
        .unwrap_or_else(|err| panic!("{}", err.render(LIB)));
}
