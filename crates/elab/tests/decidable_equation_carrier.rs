//! Acceptance for issues/decidable-equation-carrier.md. Equality instances
//! are registered by the endpoints' resolved carrier, while resolution still
//! checks the complete `Decide<a = b>` head.

use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");

fn with_std() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).expect("logic");
    e.elab_module_source("bool", BOOL).expect("bool");
    e.elab_module_source("nat", NAT).expect("nat");
    e
}

fn ok(src: &str) {
    let mut e = with_std();
    e.elab_module_source("probe", src)
        .unwrap_or_else(|error| panic!("{}", error.render(src)));
}

#[test]
fn nat_equality_drives_if_and_computes_both_answers() {
    ok(
        r#"
        import logic;
        import bool;
        import nat;

        fn same(n, m: Nat) -> Nat { if n = m { 1 } else { 0 } }
        theorem yes(): same(4, 4) = 1 { refl }
        theorem no(): same(4, 5) = 0 { refl }
        "#,
    );
}

#[test]
fn nat_and_bool_equality_instances_coexist_and_are_selected_by_type() {
    ok(
        r#"
        import logic;
        import bool;
        import nat;

        fn same_nat(n, m: Nat) -> Nat { if n = m { 1 } else { 0 } }
        fn same_bool(a, b: Bool) -> Nat { if a = b { 1 } else { 0 } }

        theorem nat_yes(): same_nat(2, 2) = 1 { refl }
        theorem nat_no(): same_nat(2, 3) = 0 { refl }
        theorem bool_yes(): same_bool(True, True) = 1 { refl }
        theorem bool_no(): same_bool(True, False) = 0 { refl }
        "#,
    );
}

#[test]
fn equality_decision_backchains_inside_a_composed_proposition() {
    ok(
        r#"
        import logic;
        import bool;
        import nat;

        fn composed(n, m: Nat) -> Nat {
            if (n = m) ∨ False { 1 } else { 0 }
        }
        theorem yes(): composed(3, 3) = 1 { refl }
        theorem no(): composed(3, 4) = 0 { refl }
        "#,
    );
}

#[test]
fn an_unregistered_endpoint_type_is_not_answered_by_nat_or_bool() {
    let src = r#"
        import logic;
        import bool;
        inductive Token { A, B }
        fn bad(x, y: Token) -> Nat { if x = y { 1 } else { 0 } }
    "#;
    let mut e = with_std();
    let msg = e
        .elab_module_source("probe", src)
        .expect_err("Token equality has no Decide instance")
        .render(src);
    assert!(msg.contains("no instance") && msg.contains("Decide"), "{msg}");
    assert!(msg.contains("x = y"), "{msg}");
}
