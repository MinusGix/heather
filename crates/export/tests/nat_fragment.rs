//! The prototype's acceptance: a few `Nat` declarations and a two-constructor
//! enum export with no refusal, and — when `HEATHER_EXPORT_OUT` names a
//! directory — are written there as `Exported.lean` / `Exported.v` beside the
//! preludes, for `scripts/export-recheck` to hand to Lean and Rocq.

use heather_elab::Elaborator;
use heather_export::{Source, Target, export, print};

const SOURCE: &str = r#"
fn Nat::add(self a: Nat, b: Nat) → Nat { match b { Zero => a, Succ(k) => Succ(a.add(k)) } }
theorem Nat::add_left_zero(self x: Nat): Nat::add(0, x) = x {
    match x { Zero => refl, Succ(k) => Nat::cong_succ(k.add_left_zero()) }
}
theorem Nat::add_succ_left(self a: Nat, b: Nat): Nat::add(Succ(a), b) = Succ(Nat::add(a, b)) {
    match b { Zero => refl, Succ(k) => Nat::cong_succ(a.add_succ_left(k)) }
}
theorem Nat::add_assoc(self x: Nat, y: Nat, z: Nat): Nat::add(Nat::add(x, y), z) = Nat::add(x, Nat::add(y, z)) {
    match z { Zero => refl, Succ(k) => Nat::cong_succ(x.add_assoc(y, k)) }
}
inductive B { T, F }
fn B::not(self b: B) -> B { match b { T => F, F => T } }
theorem B::not_not(self b: B): b.not().not() = b { match b { T => refl, F => refl } }
theorem big(): Nat::add(1000000000000000000000, 1) = 1000000000000000000001 { refl }
"#;

#[test]
fn nat_and_enum_export_without_refusal() {
    let mut e = Elaborator::with_prelude_for_export().expect("prelude");
    e.elab_source(SOURCE).expect("source checks");
    let decls = export(&Source {
        psi: e.psi(),
        proof: &|abs| e.export_proof(abs).cloned(),
        name: &|abs| e.global_key_at(abs).map(str::to_string).or_else(|| e.generated_key_at(abs)),
    });
    let refused: Vec<_> = decls.iter().filter(|d| d.decl.is_err()).collect();
    assert!(refused.is_empty(), "refused: {refused:?}");
    // Every theorem kept its proof, the prelude's included: nothing exports
    // as an assumption.
    let assumed: Vec<_> = decls.iter().filter(|d| d.decl.as_ref().is_ok_and(|d| d.body.is_none())).map(|d| &d.name).collect();
    assert!(assumed.is_empty(), "exported as axioms: {assumed:?}");
    let lean = print(Target::Lean, &decls);
    assert!(lean.contains("def Heather.main.Nat.add_assoc :"), "{lean}");
    if let Some(dir) = std::env::var_os("HEATHER_EXPORT_OUT") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::write(dir.join("Exported.lean"), lean).unwrap();
        std::fs::write(dir.join("Exported.v"), print(Target::Coq, &decls)).unwrap();
    }
}

/// An ordinary elaborator keeps no proof for a theorem whose statement
/// carries no data, so it exports as an assumption: the export mode is what
/// changes that, and it must not change what an ordinary check keeps.
#[test]
fn without_export_mode_theorems_are_assumptions() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(SOURCE).expect("source checks");
    let decls = export(&Source::psi(e.psi()));
    assert!(decls.iter().all(|d| d.decl.is_ok()));
    let assumed = decls.iter().filter(|d| d.decl.as_ref().is_ok_and(|d| d.body.is_none())).count();
    assert!(assumed >= 5, "{assumed}");
    assert!((0..e.psi().bindings.len()).all(|abs| e.export_proof(abs).is_none()));
}
