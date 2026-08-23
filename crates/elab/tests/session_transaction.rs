//! Atomicity of multi-declaration generated bundles.

use heather_elab::Elaborator;

#[test]
fn an_early_generated_declaration_does_not_survive_a_later_failure() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let psi_before = e.psi().bindings.len();
    let generated = "
inductive RolledBack { Gone }
fn generated_first() -> Nat { Zero }
theorem generated_broken(): Zero = Succ(Zero) { refl }
";

    e.elab_generated_source(generated)
        .expect_err("the generated theorem is false");
    assert_eq!(
        e.psi().bindings.len(),
        psi_before,
        "the failed bundle left ordinary or nominal globals in Ψ"
    );

    let probe = "fn probe() -> Nat { generated_first() }";
    let error = e
        .elab_source(probe)
        .expect_err("the early generated fn leaked");
    assert!(error.to_string().contains("generated_first"), "{error}");

    // The nominal and ordinary registrations were removed along with Ψ: both
    // names can be committed afresh at the positions the bundle vacated.
    e.elab_source(
        "inductive RolledBack { Gone }\n\
         fn generated_first() -> Nat { Succ(Zero) }",
    )
    .expect("the rolled-back type and declaration names should be reusable");
}
