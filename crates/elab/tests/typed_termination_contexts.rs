//! Inferred local types and dependent telescopes in decrease obligations.
use heather_elab::Elaborator;
mod support;
fn base() -> Elaborator {
    support::semantic_test_base(&[
        ("logic", include_str!("../../../lib/std/logic.hthr")),
        ("bool", include_str!("../../../lib/std/bool.hthr")),
        ("nat", include_str!("../../../lib/std/nat.hthr")),
        ("option", include_str!("../../../lib/std/option.hthr")),
        ("pair", include_str!("../../../lib/std/pair.hthr")),
        ("list", include_str!("../../../lib/std/list.hthr")),
        ("algebra", include_str!("../../../lib/std/algebra.hthr")),
        ("int", include_str!("../../../lib/std/int.hthr")),
        ("omega", include_str!("../../../lib/std/omega.hthr")),
        ("result", include_str!("../../../lib/std/result.hthr")),
    ])
}
const IMPORTS: &str = "import logic; import nat; import list; import pair; import int; import omega; import result;";
fn ok(src: &str) {
    let src = format!("{IMPORTS}\n{src}");
    base().elab_module_source("client", &src).unwrap_or_else(|e| panic!("{}", e.render(&src)));
}

#[test]
fn inferred_values_and_open_dependent_records() {
    ok(r#"
        record Remaining<A>(limit: Nat) { rest: List<A>, bound: nat::Le(list_len(rest),limit) }
        fn identity<A>(xs: List<A>) -> Remaining<A>(list_len(xs)) {
            Remaining(xs, nat::le_refl(list_len(xs)))
        }
        theorem tail_small<A>(limit: Nat, p: Remaining<A>(limit), x: A, xs: List<A>,
            shape: p.rest = Cons(x,xs)): nat::Lt(list_len(xs),limit) {
            j(shape, λ ys _ => nat::Le(list_len(ys),limit), p.bound)
        }
        fn worker<B>(xs: List<B>) -> Nat decreases list_len(xs) { count(xs) }
        fn count<B>(xs: List<B>) -> Nat decreases list_len(xs) {
            let p = identity(xs);
            match shape : p.rest {
                Nil => 0,
                Cons(x,rest) => {
                    let small = tail_small(list_len(xs),p,x,rest,shape);
                    Succ(worker(rest))
                },
            }
            on ?dec1 := small;
        }
        fn open_input<A>(xs: List<A>) -> Nat { count(xs) }
        theorem closed(): count<Nat>([2,3]) = 2 { refl }
        theorem neutral<A>(x: A): count<A>([x]) = 1 { refl }
    "#);
}

#[test]
fn a_hypothesis_type_keeps_its_match_equation() {
    ok(r#"
        fn down(n: Nat) -> Nat decreases n {
            match shape : n {
                Zero => 0,
                Succ(k) => {
                    let witness: (shape = shape) = refl;
                    down(k)
                },
            }
            on ?dec1 := (λ (p: shape = shape) => j(sym(shape), λ m _ => nat::Lt(k,m), nat::lt_succ_self(k)))(witness);
        }
        theorem closed(): down(3) = 0 { refl }
    "#);
}

#[test]
fn invalid_calls_and_evidence_do_not_escape_a_failed_group() {
    for bodies in [
        "fn a(n: Nat) -> Nat decreases n { b(n) } fn b(n: Nat) -> Nat decreases n { a(n) }",
        "fn a(n: Nat) -> Nat decreases n { b(n) } fn b(n: Nat) -> Nat decreases n { a(Succ(n)) on ?dec1 := refl; }",
        "fn a(n: Nat) -> Nat decreases n { b(n) } fn b(n: Nat) -> Nat decreases n { a([]) }",
        "fn a(n: Nat) -> nat::Lt(n,n) decreases n { b(n) } fn b(n: Nat) -> nat::Lt(n,n) decreases n { let own = a(n); own on ?dec1 := own; }",
    ] {
        let mut e = base();
        let src = format!("{IMPORTS}\n{bodies}");
        let err = e.elab_module_source("bad", &src).expect_err("invalid recursion");
        assert!(!err.render(&src).contains("panicked"));
        assert!(e.axiom_report("bad::a#obl_1").is_err(), "failed group leaked an obligation");
        // Recovery uses the same elaborator, not a fresh semantic image.
        e.elab_module_source("after", "theorem clean(n: Nat): n = n { refl }").unwrap();
        assert!(e.elab_module_source("leak", "import bad; fn leaked(n: Nat) -> Nat { a(n) }").is_err());
    }
}
