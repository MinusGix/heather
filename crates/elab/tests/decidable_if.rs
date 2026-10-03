//! Acceptance for issues/decidable-if-expression.md. `if h: P` is ordinary
//! elimination of `decide<P>()`, with the evidence named in both branch
//! scopes; `if P` without evidence is a match on the decision's bit
//! (issues/native-frontend-decided-matches.md); no Boolean/proposition
//! coercion.

use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");

// `Decide` lives in `bool`, beside the Bool its bit is.
fn with_logic() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).expect("logic");
    e.elab_module_source("bool", BOOL).expect("bool");
    e
}

fn with_std() -> Elaborator {
    let mut e = with_logic();
    e.elab_module_source("nat", NAT).expect("nat");
    e
}

fn ok(e: &mut Elaborator, src: &str) {
    e.elab_module_source("probe", src)
        .unwrap_or_else(|err| panic!("{}", err.render(src)));
}

fn bad(e: &mut Elaborator, src: &str) -> String {
    e.elab_module_source("probe", src)
        .expect_err("source must be refused")
        .render(src)
}

#[test]
fn concise_if_resolves_nat_order_and_computes_both_branches() {
    ok(
        &mut with_std(),
        r#"
        import logic;
        import bool;
        import nat;

        fn max(n, m: Nat) -> Nat { if n <= m { m } else { n } }
        theorem yes(): max(2, 5) = 5 { refl }
        theorem no(): max(5, 2) = 5 { refl }
        "#,
    );
}

#[test]
fn if_is_definitionally_the_explicit_bit_match() {
    ok(
        &mut with_std(),
        r#"
        import logic;
        import bool;
        import nat;

        fn via_if(n, m: Nat) -> Nat { if n <= m { m } else { n } }
        fn via_match(n, m: Nat) -> Nat {
            match decide_bit<nat::Nat::Le(n, m)>() { True => m, False => n }
        }
        theorem same(n, m: Nat): via_if(n, m) = via_match(n, m) { refl }
        "#,
    );
}

#[test]
fn if_with_evidence_is_definitionally_the_explicit_decision_match() {
    ok(
        &mut with_std(),
        r#"
        import logic;
        import bool;
        import nat;

        fn via_if(n, m: Nat) -> Nat { if h: n <= m { m } else { n } }
        fn via_match(n, m: Nat) -> Nat {
            match decide<nat::Nat::Le(n, m)>() { Inl(h) => m, Inr(h) => n }
        }
        theorem same(n, m: Nat): via_if(n, m) = via_match(n, m) { refl }
        "#,
    );
}

// A connective's bit is the Bool connective of its operands' bits, so an
// `if` on `P ∧ Q` is a match on `x && y`.
#[test]
fn a_connective_if_matches_on_the_connective_of_bits() {
    ok(
        &mut with_std(),
        r#"
        import logic;
        import bool;
        import nat;

        fn both(n, m: Nat) -> Nat { if n <= m ∧ ¬(m <= n) { 1 } else { 0 } }
        theorem same(n, m: Nat): both(n, m) = match decide_bit<nat::Nat::Le(n, m)>() && !decide_bit<nat::Nat::Le(m, n)>() { True => 1, False => 0 } { refl }
        theorem low(): both(1, 2) = 1 { refl }
        theorem tie(): both(2, 2) = 0 { refl }
        "#,
    );
}

#[test]
fn one_evidence_name_has_the_branch_local_proof_and_refutation_types() {
    ok(
        &mut with_std(),
        r#"
        import logic;
        import bool;
        import nat;

        theorem decided(n, m: Nat): n <= m ∨ ¬ (n <= m) {
            if h : n <= m { Inl(h) } else { Inr(h) }
        }
        "#,
    );
}

#[test]
fn motive_synthesis_follows_the_decision_hidden_by_a_defined_result() {
    ok(
        &mut with_logic(),
        r#"
        import logic;
        import bool;

        fn choose<P: Decide>(x, y: Nat) -> Nat {
            if h : P { y } else { x }
        }

        theorem choose_yes<P: Decide>(x, y: Nat, p: P): choose<P>(x, y) = y {
            if h : P { refl } else { false_elim(h(p)) }
        }

        theorem choose_no<P: Decide>(x, y: Nat, np: ¬P): choose<P>(x, y) = x {
            if h : P { false_elim(np(h)) } else { refl }
        }
        "#,
    );
}

// A function an evidence-free `if` defines is reasoned about on its bit,
// with each side's evidence from `decide_bit_split`.
#[test]
fn a_bit_if_is_split_with_its_evidence() {
    ok(
        &mut with_logic(),
        r#"
        import logic;
        import bool;

        fn choose<P: Decide>(x, y: Nat) -> Nat {
            if P { y } else { x }
        }

        theorem choose_yes<P: Decide>(x, y: Nat, p: P): choose<P>(x, y) = y {
            decide_bit_split<P>(λ c => (match c { True => y, False => x }) = y, λ _ => refl, λ np => false_elim(np(p)))
        }
        "#,
    );
}

#[test]
fn a_local_decide_dictionary_wins_without_a_global_instance() {
    ok(
        &mut with_logic(),
        r#"
        import logic;
        import bool;

        theorem local<P>(d: Decide<P>): P ∨ ¬P {
            if h : P { Inl(h) } else { Inr(h) }
        }
        "#,
    );
}

#[test]
fn branch_blocks_support_local_computation() {
    ok(
        &mut with_std(),
        r#"
        import logic;
        import bool;
        import nat;

        fn f(n: Nat) -> Nat {
            if n <= 3 {
                let x = n + 1;
                x + 1
            } else {
                let x = n + 2;
                x + 2
            }
        }
        theorem low(): f(2) = 4 { refl }
        theorem high(): f(5) = 9 { refl }
        "#,
    );
}

#[test]
fn missing_decide_reports_the_resolution_trace_at_the_condition() {
    let src = r#"
        import logic;
        import bool;
        inductive Mystery { M }
        fn bad() -> Nat { if Mystery { 1 } else { 0 } }
    "#;
    let msg = bad(&mut with_logic(), src);
    assert!(msg.contains("no instance") && msg.contains("Decide"), "{msg}");
    assert!(msg.contains("Mystery"), "{msg}");
}

#[test]
fn bool_is_data_and_is_not_coerced_to_a_proposition() {
    let src = r#"
        import logic;
        import bool;
        fn bad(b: Bool) -> Nat { if b { 1 } else { 0 } }
    "#;
    let msg = bad(&mut with_std(), src);
    assert!(msg.contains("unknown type `b`") || msg.contains("not a type"), "{msg}");
}

#[test]
fn ordinary_if_infers_a_constant_branch_type() {
    ok(
        &mut with_logic(),
        r#"
        import logic;
        import bool;
        fn good() -> Nat {
            let x = if True { 1 } else { 0 };
            x
        }
        theorem computes(): good() = 1 { refl }
        theorem direct(): (if True { 1 } else { 0 }) = 1 { refl }
        "#,
    );
}
