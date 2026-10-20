//! The prototype's acceptance: a few `Nat` declarations and a two-constructor
//! enum export with no refusal, and — when `HEATHER_EXPORT_OUT` names a
//! directory — are written there as `Exported.lean` / `Exported.v` beside the
//! preludes, for `scripts/export-recheck` to hand to Lean and Rocq.

use heather_elab::Elaborator;
use heather_export::{Target, export, print};

// Proofs are written as `fn`s: a theorem whose statement carries no data
// keeps no proof in Ψ (elab `sealing::carries_data`), so it would export as
// an axiom (`issues/export-keeps-proofs.md`).
const SOURCE: &str = r#"
fn Nat::add(self a: Nat, b: Nat) → Nat { match b { Zero => a, Succ(k) => Succ(a.add(k)) } }
fn Nat::add_left_zero(self x: Nat) -> Nat::add(0, x) = x {
    match x { Zero => refl, Succ(k) => Nat::cong_succ(k.add_left_zero()) }
}
fn Nat::add_succ_left(self a: Nat, b: Nat) -> Nat::add(Succ(a), b) = Succ(Nat::add(a, b)) {
    match b { Zero => refl, Succ(k) => Nat::cong_succ(a.add_succ_left(k)) }
}
fn Nat::add_assoc(self x: Nat, y: Nat, z: Nat) -> Nat::add(Nat::add(x, y), z) = Nat::add(x, Nat::add(y, z)) {
    match z { Zero => refl, Succ(k) => Nat::cong_succ(x.add_assoc(y, k)) }
}
inductive B { T, F }
fn B::not(self b: B) -> B { match b { T => F, F => T } }
fn B::not_not(self b: B) -> b.not().not() = b { match b { T => refl, F => refl } }
fn big() -> Nat::add(1000000000000000000000, 1) = 1000000000000000000001 { refl }
"#;

#[test]
fn nat_and_enum_export_without_refusal() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(SOURCE).expect("source checks");
    let decls = export(e.psi());
    let refused: Vec<_> = decls.iter().filter(|(_, d)| d.is_err()).collect();
    // The prelude's `sym`/`trans`/`cong` are theorems: they export as axioms
    // (no proof kept), which is allowed; nothing may be refused.
    assert!(refused.is_empty(), "refused: {refused:?}");
    if let Some(dir) = std::env::var_os("HEATHER_EXPORT_OUT") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::write(dir.join("Exported.lean"), print(Target::Lean, &decls)).unwrap();
        std::fs::write(dir.join("Exported.v"), print(Target::Coq, &decls)).unwrap();
    }
}
