//! No-confusion on the `IWf` route's families, both forms
//! (`docs/kernel/iwf-infinitary-design.md` §13): `absurd` between two constructors
//! and `inj` at a payload field, kernel-checked, at literal and open data,
//! at literal and open indices, with negative controls.

use heather_elab::{Elaborator, IndexedRoute};

use crate::support::{assert_refused, Refusal};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn refused(name: &str, src: &str, why: Refusal) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert_refused(&mut e, name, src, why)
}

const ADD: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
"#;

/// The `W` form: a payload beside a function child (`RB`), and a function
/// child beside a plain one (`RC`, the stored `k̄`).
const RT: &str = r#"
inductive Rt : (n: Nat) -> Type {
    RL(x: Nat)                                        : Rt(0),
    RB(n: Nat, x: Nat, k: (y: Nat) -> Rt(add(y, n)))  : Rt(Succ(n)),
    RC(n: Nat, k: (y: Nat) -> Rt(n), l: Rt(n))        : Rt(n),
}
"#;

/// The kernel `IWf` form (`iwf_match_tiers.rs`'s `T`, with a payload).
const PT: &str = r#"
inductive Pt : (n: Nat) -> Type {
    PL(x: Nat)                               : Pt(0),
    PN(n: Nat, x: Nat, l: Pt(0), r: Pt(n))   : Pt(Succ(n)),
    PM(n: Nat, r: Pt(n))                     : Pt(Succ(n)),
}
"#;

#[test]
fn the_families_are_on_the_routes_under_test() {
    let e = elab(&format!("{ADD}{RT}{PT}"));
    assert_eq!(e.indexed_route("Rt"), Some(IndexedRoute::IwfW));
    assert_eq!(e.indexed_route("Pt"), Some(IndexedRoute::Iwf));
}

// Disjointness at a literal index and at an open one, on open data: the tag
// predicate eliminates at any index, and β fires on the constructor there.
#[test]
fn absurd_on_the_w_form() {
    elab(&format!(
        "{ADD}{RT}
         theorem l_c(a: Nat, k: (y: Nat) -> Rt(0), l: Rt(0), p: RL(a) = RC(0, k, l)): 0 = 1 {{ absurd(p) }}
         theorem b_c(n: Nat, a: Nat, f: (y: Nat) -> Rt(add(y, n)), k: (y: Nat) -> Rt(Succ(n)), l: Rt(Succ(n)),
                     p: RB(n, a, f) = RC(Succ(n), k, l)): Nat {{ absurd(p) }}
         theorem c_l(k: (y: Nat) -> Rt(0), p: RC(0, k, RL(1)) = RL(2)): 1 = 2 {{ absurd(p) }}"
    ));
}

#[test]
fn absurd_on_the_iwf_form() {
    elab(&format!(
        "{PT}
         theorem n_m(n: Nat, x: Nat, l: Pt(0), r: Pt(n), s: Pt(n), p: PN(n, x, l, r) = PM(n, s)): 0 = 1 {{ absurd(p) }}
         theorem lit(p: PM(0, PL(1)) = PN(0, 2, PL(3), PL(4))): Nat {{ absurd(p) }}"
    ));
}

// Injectivity at a payload field, as declared (field index counts children
// too): the result is the field equation, at open and literal data.
#[test]
fn inj_at_a_payload_field_on_the_w_form() {
    elab(&format!(
        "{ADD}{RT}
         theorem l_inj(a: Nat, b: Nat, p: RL(a) = RL(b)): a = b {{ inj(p, 0) }}
         theorem b_inj(n: Nat, a: Nat, b: Nat, f: (y: Nat) -> Rt(add(y, n)), g: (y: Nat) -> Rt(add(y, n)),
                       p: RB(n, a, f) = RB(n, b, g)): a = b {{ inj(p, 1) }}
         theorem b_idx(n: Nat, a: Nat, b: Nat, f: (y: Nat) -> Rt(add(y, n)), g: (y: Nat) -> Rt(add(y, n)),
                       p: RB(n, a, f) = RB(n, b, g)): n = n {{ inj(p, 0) }}
         theorem l_lit(p: RL(3) = RL(3)): 3 = 3 {{ inj(p, 0) }}"
    ));
}

#[test]
fn inj_at_a_payload_field_on_the_iwf_form() {
    elab(&format!(
        "{PT}
         theorem n_inj(n: Nat, x: Nat, y: Nat, l: Pt(0), r: Pt(n), s: Pt(n), p: PN(n, x, l, r) = PN(n, y, l, s)): x = y {{ inj(p, 1) }}
         theorem l_inj(a: Nat, b: Nat, p: PL(a) = PL(b)): a = b {{ inj(p, 0) }}"
    ));
}

// The results compose: a contradiction from a payload disagreement, through
// `inj` and then `Nat`'s own `absurd`.
#[test]
fn inj_then_absurd_refutes_a_payload_disagreement() {
    elab(&format!(
        "{ADD}{RT}{PT}
         theorem rt(p: RL(0) = RL(1)): Nat {{ absurd(inj(p, 0)) }}
         theorem pt(l: Pt(0), r: Pt(0), p: PN(0, 0, l, r) = PN(0, 1, l, r)): Nat {{ absurd(inj(p, 1)) }}"
    ));
}

// Negative controls: each refusal names its reason.
#[test]
fn absurd_between_one_constructor_is_refused() {
    refused(
        "same",
        &format!("{ADD}{RT}\ntheorem s(a: Nat, b: Nat, p: RL(a) = RL(b)): Nat {{ absurd(p) }}"),
        Refusal::Says("both sides of this equation are `RL`, so it is not absurd"),
    );
}

#[test]
fn inj_between_two_constructors_is_refused() {
    refused(
        "two",
        &format!("{PT}\ntheorem t(n: Nat, x: Nat, l: Pt(0), r: Pt(n), s: Pt(n), p: PN(n, x, l, r) = PM(n, s)): Nat {{ inj(p, 0) }}"),
        Refusal::Says("which are different constructors"),
    );
}

#[test]
fn inj_at_a_recursive_field_is_refused() {
    refused(
        "child",
        &format!(
            "{ADD}{RT}\ntheorem c(k: (y: Nat) -> Rt(0), l: Rt(0), m: Rt(0), p: RC(0, k, l) = RC(0, k, m)): l = m {{ inj(p, 2) }}"
        ),
        Refusal::Says("`inj` at the recursive field of `RC` is not supported"),
    );
    refused(
        "child_iwf",
        &format!("{PT}\ntheorem c(r: Pt(0), s: Pt(0), p: PM(0, r) = PM(0, s)): r = s {{ inj(p, 1) }}"),
        Refusal::Says("`inj` at the recursive field of `PM` is not supported"),
    );
}

#[test]
fn a_neutral_side_is_not_a_constructor() {
    refused(
        "neutral",
        &format!("{ADD}{RT}\ntheorem n(t: Rt(0), p: t = RL(0)): Nat {{ absurd(p) }}"),
        Refusal::Says("needs both sides of the equation to be constructor applications"),
    );
}

// A wrong claim from a right equation is still refused: `inj` gives the
// field equation, not anything else.
#[test]
fn inj_proves_only_the_field_equation() {
    refused(
        "wrong",
        &format!("{ADD}{RT}\ntheorem w(a: Nat, b: Nat, p: RL(a) = RL(b)): a = 0 {{ inj(p, 0) }}"),
        Refusal::Mismatch,
    );
}

// A literal side reports its field as written, not as its reduct: the
// result is the equation the user wrote down, usable where that spelling is.
#[test]
fn inj_reports_the_fields_as_written() {
    elab(&format!(
        "{ADD}{RT}
         theorem w(p: RL(add(1, 2)) = RL(add(2, 1))): add(1, 2) = add(2, 1) {{ inj(p, 0) }}"
    ));
}

/// `cp` rebuilds every node and `sz` takes it apart, so the arm's goal
/// reduces to `sz`'s reduct on `cp`'s constructor, which carries the
/// constructor's pieces as `cp` spelled them; the proof's endpoints carry
/// the arm's own. Plain `cong` finds the congruence up to conversion
/// (issues/cong-inference-through-iwf-w-children.md).
const SZ_IWF: &str = r#"
fn sz(n: Nat, t: Pt(n)) -> Nat { match t { PL(x) => 1, PN(m, x, l, r) => Succ(sz(m, r)), PM(m, r) => Succ(sz(m, r)) } }
fn cp(n: Nat, t: Pt(n)) -> Pt(n) { match t { PL(x) => PL(x), PN(m, x, l, r) => PN(m, x, l, cp(m, r)), PM(m, r) => PM(m, cp(m, r)) } }
"#;

const SZ_W: &str = r#"
fn sz(n: Nat, t: Rt(n)) -> Nat {
    match t { RL(x) => 1, RB(m, x, k) => Succ(sz(add(0, m), k(0))), RC(m, k, l) => Succ(sz(m, l)) }
}
fn cp(n: Nat, t: Rt(n)) -> Rt(n) {
    match t { RL(x) => RL(x), RB(m, x, k) => RB(m, x, λ y => cp(add(y, m), k(y))), RC(m, k, l) => RC(m, λ y => cp(m, k(y)), cp(m, l)) }
}
"#;

#[test]
fn plain_cong_inside_arms_on_the_iwf_form() {
    elab(&format!(
        "{PT}{SZ_IWF}
         theorem cs(n: Nat, t: Pt(n)): sz(n, cp(n, t)) = sz(n, t) {{
             match t {{ PL(x) => refl, PN(m, x, l, r) => cong(cs(m, r)), PM(m, r) => cong(cs(m, r)) }}
         }}"
    ));
}

#[test]
fn plain_cong_inside_arms_on_the_w_form() {
    // Through a function child at its rebound index (`RB`), and through the
    // stored children `k̄` (`RC`), whose goal reduces through the
    // stored-children transport (issues/elab-whnf-family-transport-cost.md).
    elab(&format!(
        "{ADD}{RT}{SZ_W}
         theorem cs(n: Nat, t: Rt(n)): sz(n, cp(n, t)) = sz(n, t) {{
             match t {{
                 RL(x) => refl,
                 RB(m, x, k) => cong(cs(add(0, m), k(0))),
                 RC(m, k, l) => cong(cs(m, l)),
             }}
         }}"
    ));
}

// The widened witness test still refuses what is not a congruence: here the
// goal's sides differ by a `Succ` the proof does not account for, and the
// message is the one `cong` always gave.
#[test]
fn cong_still_refuses_a_goal_that_is_not_a_congruence() {
    refused(
        "not_cong",
        &format!(
            "{PT}{SZ_IWF}
             theorem cs(n: Nat, t: Pt(n)): sz(n, cp(n, t)) = sz(n, t) {{
                 match t {{ PL(x) => refl, PN(m, x, l, r) => cong(cs(m, r)), PM(m, r) => cong(cs(m, r)) }}
             }}
             theorem bad(n: Nat, t: Pt(n)): Succ(sz(n, cp(n, t))) = sz(n, t) {{ cong(cs(n, t)) }}"
        ),
        Refusal::Says("cannot generalize"),
    );
}
