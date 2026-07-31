//! `lib/ir_v1.hthr` — FunctionIR v1 and `simulate` — under `scripts/test`.
//!
//! The library file is the deliverable of docs/ir-simulate-design.md §11
//! items 1, 2 and 6. Its conversion cost is real and measured
//! (issues/simulate-conversion-cost.md): ~107s in a release build for the
//! full file, ~10x that under the debug profile `cargo test` uses — which
//! does not fit `scripts/test`'s 300 CPU-second budget. So the split here:
//!
//! - the always-on test elaborates every DECLARATION (datatypes, helpers,
//!   the interpreter, the add program) and runs the one negative control
//!   the file cannot state about itself — a wrong simulate claim must be
//!   refuted — at the cheapest possible depth;
//! - the full acceptance (the file's own theorems) is `#[ignore]`d, run
//!   explicitly via `scripts/test -- --ignored` when touching this area,
//!   and routinely via `target/release/heather check lib/ir_v1.hthr`.

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

/// The full library, acceptance theorems included. ~18 minutes under the
/// debug profile — see the module comment for when and how to run it.
#[test]
#[ignore = "conversion-heavy (issues/simulate-conversion-cost.md); run via scripts/test -- --ignored, or release heather check"]
fn the_full_ir_library_checks() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(LIB)
        .unwrap_or_else(|err| panic!("{}", err.render(LIB)));
}
