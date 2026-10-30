//! Automatic local evidence for well-founded recursion.
use heather_elab::Elaborator;
use crate::support;
fn base() -> Elaborator {
    support::semantic_test_base(&[
        ("logic", include_str!("../../../lib/std/core/logic.hthr")),
        ("bool", include_str!("../../../lib/std/core/bool.hthr")),
        ("nat", include_str!("../../../lib/std/num/nat.hthr")),
        ("option", include_str!("../../../lib/std/core/option.hthr")),
        ("pair", include_str!("../../../lib/std/core/pair.hthr")),
        ("list", include_str!("../../../lib/std/data/list.hthr")),
        ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
        ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
        ("int", include_str!("../../../lib/std/num/int.hthr")),
        ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
        ("result", include_str!("../../../lib/std/core/result.hthr")),
    ])
}
const IMPORTS: &str = "import logic; import nat; import list; import pair;";
fn ok(src: &str) {
    let src = format!("{IMPORTS}\n{src}");
    base().elab_module_source("client", &src).unwrap_or_else(|e| panic!("{}", e.render(&src)));
}

#[test]
fn direct_evidence_works_without_omega_and_ignores_untyped_locals() {
    ok(r#"
        fn use(f: Nat → Nat) -> Nat { f(0) }
        fn down(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => use(λ unrelated => {
                    let irrelevant: nat::Nat::Le(unrelated,unrelated) = nat::Nat::le_refl(unrelated);
                    let small: nat::Nat::Lt(k,Succ(k)) = nat::Nat::lt_succ_self(k);
                    down(k)
                }),
            }
        }
        theorem closed(): down(3) = 0 { refl }
        theorem neutral(n: Nat): down(n) = down(n) { refl }
    "#);
}

#[test]
fn an_exposed_dependent_record_field_supplies_progress() {
    ok(r#"
        record Progress(limit: Nat) { next: Nat, bound: nat::Nat::Lt(next,limit) }
        fn down(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => {
                    let p: Progress(Succ(k)) = Progress(k,nat::Nat::lt_succ_self(k));
                    let small = p.bound;
                    down(p.next)
                },
            }
        }
        theorem closed(): down(3) = 0 { refl }
    "#);
}

#[test]
fn arithmetic_combines_relevant_local_facts() {
    ok(r#"
        import int; import omega;
        fn down(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => {
                    let smaller: Nat = k;
                    let step: (smaller < Succ(k)) = nat::Nat::lt_succ_self(k);
                    let next: Nat = smaller;
                    let bound: (next <= smaller) = nat::Nat::le_refl(smaller);
                    down(next)
                },
            }
        }
        theorem closed(): down(4) = 0 { refl }
    "#);
}

#[test]
fn false_reversed_insufficient_and_circular_evidence_is_refused() {
    for src in [
        "fn bad(n: Nat) -> Nat decreases n { let weak = nat::Nat::le_refl(n); bad(n) }",
        "fn bad(n: Nat) -> Nat decreases n { let reversed = nat::Nat::lt_succ_self(n); bad(Succ(n)) }",
        "fn bad(n: Nat) -> Nat decreases n { let false_proof: nat::Nat::Lt(n,n) = refl; bad(n) }",
        "fn bad(n: Nat) -> nat::Nat::Lt(n,n) decreases n { let own = bad(n); own }",
        "fn bad(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => { let good = nat::Nat::lt_succ_self(k); bad(k) } } on ?dec1 := refl; }",
    ] {
        let mut e = base();
        let src = format!("{IMPORTS} import int; import omega; {src}");
        let err = e.elab_module_source("bad", &src).expect_err("invalid evidence");
        assert!(!err.render(&src).contains("panicked"));
        e.elab_module_source("after", "theorem clean(n: Nat): n = n { refl }").unwrap();
    }
}
