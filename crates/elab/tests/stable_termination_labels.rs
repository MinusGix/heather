//! Automatic local evidence for well-founded recursion.
use heather_elab::Elaborator;
use crate::support;
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
const IMPORTS: &str = "import logic; import nat; import list; import pair;";
fn ok(src: &str) {
    let src = format!("{IMPORTS}\n{src}");
    base().elab_module_source("client", &src).unwrap_or_else(|e| panic!("{}", e.render(&src)));
}

#[test]
fn labels_survive_insertion_reordering_and_nesting() {
    for body in [
        "down(k,0) decreasing tail",
        "{ let earlier = down(k,0); down(k,earlier) decreasing tail }",
        "down(k,down(k,0) decreasing inner) decreasing tail",
    ] {
        let inner = if body.contains("decreasing inner") { "on decreasing inner := nat::Nat::lt_succ_self(k);" }
            else if body.contains("earlier") { "on ?dec1 := nat::Nat::lt_succ_self(k);" } else { "" };
        ok(&format!(r#"
            fn down(n: Nat, extra: Nat) -> Nat decreases n {{
                match n {{ Zero => 0, Succ(k) => {body} }}
                on decreasing tail := nat::Nat::lt_succ_self(k);
                {inner}
            }}
            theorem closed(): down(3,0) = 0 {{ refl }}
        "#));
    }
    for order in ["let a = down(k) decreasing first; let b = down(k) decreasing second;", "let b = down(k) decreasing second; let a = down(k) decreasing first;"] {
        ok(&format!(r#"
            fn down(n: Nat) -> Nat decreases n {{
                match n {{ Zero => 0, Succ(k) => {{ {order} a }} }}
                on decreasing first := nat::Nat::lt_succ_self(k);
                on decreasing second := nat::Nat::lt_succ_self(k);
            }}
            theorem closed(): down(2) = 0 {{ refl }}
        "#));
    }
}

#[test]
fn mutual_labels_are_per_declaration_and_keep_open_types() {
    ok(r#"
        import int; import omega;
        fn first<A>(n: Nat, x: A) -> A decreases n {
            second(n,x) decreasing step
            on decreasing step := nat::Nat::le_refl(n);
        }
        fn second<A>(n: Nat, x: A) -> A decreases n {
            match n { Zero => x, Succ(k) => first(k,x) decreasing step }
            on decreasing step := nat::Nat::lt_succ_self(k);
        }
        theorem neutral<A>(x: A): first(3,x) = x { refl }
    "#);
}

#[test]
fn labels_survive_result_propagation_and_do_not_capture_goal_names() {
    ok(r#"
        import result;
        fn down(n: Nat) -> Result<Nat,Nat> decreases n {
            match n {
                Zero => Ok(0),
                Succ(k) => {
                    let x = (down(k) decreasing tail)?;
                    let y: Nat = ?tail;
                    Ok(x)
                },
            }
            on decreasing tail := nat::Nat::lt_succ_self(k);
            on ?tail := 7;
        }
        theorem closed(): down(2) = Ok<Nat,Nat>(0) { refl }
    "#);
}

#[test]
fn label_errors_are_scoped_and_wrong_evidence_is_rejected() {
    for (src, message) in [
        ("fn bad(n: Nat) -> Nat decreases n { bad(n) decreasing x on decreasing y := refl; }", "unknown decrease label `y`"),
        ("fn bad(n: Nat) -> Nat decreases n { bad(bad(n) decreasing x) decreasing x }", "duplicate decrease label `x`"),
        ("fn bad(n: Nat) -> Nat decreases n { bad(n) decreasing x on decreasing x := refl; on decreasing x := refl; }", "duplicate discharge"),
        ("fn bad(n: Nat) -> Nat decreases n { Succ(n) decreasing x }", "must name a call"),
        ("fn bad(n: Nat) -> Nat { Succ(n) decreasing x }", "needs a declaration with `decreases`"),
    ] {
        let src = format!("{IMPORTS} {src}");
        let mut e = base();
        let error = e.elab_module_source("bad", &src).expect_err("invalid label").render(&src);
        assert!(error.contains(message), "{error}");
        e.elab_module_source("after", "theorem clean(n: Nat): n = n { refl }").unwrap();
    }
    // The proof fits the first site's goal, but the named second call does
    // not decrease. A traversal-order mix-up must not accept it.
    let src = format!(r#"{IMPORTS}
        fn bad(n: Nat) -> Nat decreases n {{
            match n {{ Zero => 0, Succ(k) => {{
                let first = bad(k) decreasing good;
                bad(Succ(k)) decreasing wrong
            }} }}
            on decreasing good := nat::Nat::lt_succ_self(k);
            on decreasing wrong := nat::Nat::lt_succ_self(k);
        }}
    "#);
    assert!(base().elab_module_source("bad", &src).is_err());
}

#[test]
fn unsolved_labels_use_the_source_spelling() {
    let src = format!("{IMPORTS} fn bad(n: Nat) -> Nat decreases n {{ bad(n) decreasing tail }}");
    let error = base().elab_module_source("bad", &src).unwrap_err().render(&src);
    assert!(error.contains("decreasing tail"), "{error}");
    assert!(!error.contains("#decreasing:"), "{error}");
}
