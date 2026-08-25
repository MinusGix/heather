//! Explicit assumptions are visible at the surface and remain traceable after
//! theorem proofs become opaque.

use heather_elab::{AssumptionKind, Elaborator};

#[test]
fn direct_and_transitive_paths_are_reported() {
    let mut e = Elaborator::new();
    e.elab_source(
        "axiom oracle(): Nat;\n\
         theorem direct(): Nat { oracle() }\n\
         theorem indirect(): Nat { direct() }\n\
         theorem clean(): Nat { 0 }",
    )
    .unwrap();

    let direct = e.axiom_report("direct").unwrap();
    assert_eq!(direct.direct, ["main::oracle"]);
    assert_eq!(direct.axioms[0].kind, AssumptionKind::User);
    assert_eq!(direct.axioms[0].path, ["main::direct", "main::oracle"]);

    let indirect = e.axiom_report("indirect").unwrap();
    assert_eq!(indirect.direct, ["main::direct"]);
    assert_eq!(
        indirect.axioms[0].path,
        ["main::indirect", "main::direct", "main::oracle"]
    );
    assert!(e.axiom_report("clean").unwrap().axioms.is_empty());
}

#[test]
fn unused_axioms_and_statement_only_mentions_do_not_taint_a_proof() {
    let mut e = Elaborator::new();
    e.elab_source(
        "axiom witness(): Nat;\n\
         theorem says_something_about_it(): witness() = witness() { refl }\n\
         theorem unrelated(): Nat { 0 }",
    )
    .unwrap();
    assert!(e.axiom_report("says_something_about_it").unwrap().axioms.is_empty());
    assert!(e.axiom_report("unrelated").unwrap().axioms.is_empty());
}

#[test]
fn paths_use_resolved_module_identity() {
    let mut e = Elaborator::new();
    e.elab_module_source("trusted", "axiom seed(): Nat; theorem via(): Nat { seed() }")
        .unwrap();
    e.elab_module_source(
        "client",
        "import trusted; theorem result(): Nat { via() }",
    )
    .unwrap();
    let r = e.axiom_report("client::result").unwrap();
    assert_eq!(
        r.axioms[0].path,
        ["client::result", "trusted::via", "trusted::seed"]
    );
}

#[test]
fn a_failed_generated_bundle_rolls_provenance_back() {
    let mut e = Elaborator::new();
    let err = e.elab_generated_source(
        "axiom generated_trust(): Nat; theorem broken(): 0 = 1 { refl }",
    );
    assert!(err.is_err());
    assert!(e.axiom_report("generated_trust").is_err());
}

#[test]
fn shortest_path_is_deterministic_when_two_routes_reach_one_axiom() {
    let mut e = Elaborator::new();
    e.elab_source(
        "axiom root(): Nat;\n\
         theorem zroute(): Nat { root() }\n\
         theorem aroute(): Nat { root() }\n\
         fn choose(x: Nat) -> Nat { match x { Zero => aroute(), Succ(_) => zroute() } }",
    )
    .unwrap();
    let r = e.axiom_report("choose").unwrap();
    assert_eq!(r.direct, ["main::aroute", "main::zroute"]);
    assert_eq!(r.axioms[0].path, ["main::choose", "main::aroute", "main::root"]);
}

#[test]
fn synthesized_instance_globals_carry_provenance() {
    let mut e = Elaborator::with_prelude().unwrap();
    e.elab_source(
        "class Mag<A> { op: A -> A -> A }\n\
         inductive Z { Z0 }\n\
         axiom trusted(): Z;\n\
         instance Mag<Z> { fn op(x: Z, y: Z) -> Z { trusted() } }\n\
         fn combine<A> requires m: Mag<A> (x: A, y: A) -> A { m.op(x, y) }\n\
         fn use(x: Z, y: Z) -> Z { combine(x, y) }",
    )
    .unwrap();
    let r = e.axiom_report("use").unwrap();
    assert_eq!(r.axioms.len(), 1);
    assert_eq!(r.axioms[0].axiom, "main::trusted");
    assert!(
        r.axioms[0].path.iter().any(|name| name.contains("Mag")),
        "the path should expose the synthesized instance declarations: {:?}",
        r.axioms[0].path
    );
}

#[test]
fn an_axiom_statement_cannot_hide_an_unsolved_goal() {
    let mut e = Elaborator::new();
    let errs = e.check_source("axiom incomplete(): ?statement;");
    assert_eq!(errs.len(), 1);
    assert!(errs[0].to_string().contains("hole"), "{}", errs[0]);
    assert!(e.axiom_report("incomplete").is_err());
}
