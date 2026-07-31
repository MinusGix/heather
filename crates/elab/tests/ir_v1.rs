//! `lib/ir_v1.hthr` — FunctionIR v1 and `simulate` — under `scripts/test`.
//!
//! The library file is the deliverable of docs/ir-simulate-design.md §11
//! items 1, 2 and 6. Both tests here run under `scripts/test`: the release
//! check went 107s → 13.6s (closed subtrees) → ~2.4s (definitions,
//! issues/simulate-conversion-cost.md) → **1.25s** (the value domain,
//! issues/nbe-conversion-round.md), and this file's whole debug run is
//! **9.2s** against the 300 CPU-second budget. That headroom is why the
//! library now carries the two combined LetCall-into-the-loop theorems
//! whose exponential cost used to keep them out entirely; they are ~10% of
//! the release check. The split is kept because the two tests answer
//! different questions:
//!
//! - the first elaborates every DECLARATION (datatypes, helpers, the
//!   interpreter, the add program) and runs the one negative control the
//!   file cannot state about itself — a wrong simulate claim must be
//!   refuted — at the cheapest possible depth;
//! - the second is the full acceptance, the file's own theorems.

use heather_elab::Elaborator;

const LIB: &str = include_str!("../../../lib/ir_v1.hthr");

/// Everything up to the first theorem: the acceptance theorems are all in
/// the file's final section, so this is exactly the declarations.
fn decls() -> &'static str {
    let cut = LIB.find("\ntheorem ").expect("the library has theorems");
    &LIB[..cut]
}

#[test]
fn declarations_check_and_a_wrong_claim_is_refuted() {
    let src = decls();
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src)
        .unwrap_or_else(|err| panic!("{}", err.render(src)));

    // Zero fuel is OutOfFuel; claiming it produced a value must fail. One
    // eval unfolding, so the control costs seconds, not minutes.
    let wrong = "theorem wrong(): eval(0, PNil)(VNil, Ret(RNil)) = Out(VNil) { refl }";
    match e.elab_source(wrong) {
        // `refl` at a false equation dies in the kernel as NotConvertible
        Err(err) => {
            let msg = format!("{err}");
            assert!(msg.contains("NotConvertible"), "unexpected refutation: {msg}");
        }
        Ok(()) => panic!("a false simulate claim elaborated"),
    }
}

/// The full library, acceptance theorems included — the deep combined
/// theorems among them. 9.2s under the debug profile (was ~18, then ~60 when
/// the file grew); the release `heather check` is 1.25s.
#[test]
fn the_full_ir_library_checks() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(LIB)
        .unwrap_or_else(|err| panic!("{}", err.render(LIB)));
}
