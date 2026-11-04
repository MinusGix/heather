//! Acceptance for issues/omega-atoms-up-to-computation.md and its Int half,
//! issues/omega-int-atoms-up-to-computation.md: an atom that
//! computes to a numeral is that constant, and an atom that converts to one
//! already in the table is that atom, instead of each spelling being a
//! variable of its own. The positives are the issue's two one-liners (a
//! closed numeral under a global head; a local head over an argument that
//! computes), plus the same argument computing inside an **open** element
//! type and a closed atom met in a *checking* position. The controls pin what
//! computation must not merge: arguments that compute to different values
//! stay two atoms, and so do distinct variables. The Int rows repeat the
//! same positives and controls at an Int-valued head, with a closed atom on
//! each side of zero.

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/tactic/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", ALGEBRA),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", INT),
    ("omega", OMEGA),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn load_image() -> SemanticImage {
    // Built once per process (`BASE` is a process-wide `OnceLock`; the other
    // tests wait for it): see `support`'s note on per-test threads.
    support::semantic_test_base(MODULES).semantic_image()
}

fn base() -> Elaborator {
    BASE.get_or_init(load_image).elaborator()
}

const IMPORTS: &str = "import logic;\nimport nat;\nimport list;\nimport int;\nimport omega;\n";

fn ok(src: &str) {
    let mut e = base();
    e.elab_module_source("m", &format!("{IMPORTS}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}"));
}

fn elab_err(src: &str) -> String {
    let mut e = base();
    match e.elab_module_source("m", &format!("{IMPORTS}{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

#[test]
fn a_closed_atom_that_computes_is_its_numeral() {
    ok("theorem closed_bit(x: Nat, h: Nat::of_bit(True) + x = 0): False { omega }");
}

#[test]
fn a_closed_atom_in_the_goal_is_its_numeral() {
    ok("theorem bits(x: Nat, h: x < Nat::of_bit(True)): x + Nat::of_bit(False) = 0 { omega }");
}

#[test]
fn an_argument_that_computes_meets_the_atom_it_computes_to() {
    ok("theorem appended(f: List<Nat> → Nat, h: f(list::List::append(Nil, Nil)) = f(Nil) + f(Nil)): f(Nil) = 0 { omega }");
}

#[test]
fn the_argument_computes_at_an_open_element_type() {
    ok("theorem appended_at<A>(f: List<A> → Nat, xs: List<A>, h: f(list::List::append(Nil, xs)) + 1 = f(xs)): False { omega }");
}

#[test]
fn arguments_computing_to_different_values_stay_two_atoms() {
    let msg = elab_err(
        "theorem distinct(f: List<Nat> → Nat, h: f(Cons(0, Nil)) = f(list::List::append(Nil, Nil)) + 1): f(Nil) = 0 { omega }",
    );
    assert!(msg.contains("got stuck"), "{msg}");
    assert!(msg.contains("f(Cons(0, Nil))"), "{msg}");
}

#[test]
fn distinct_variables_stay_two_atoms() {
    let msg = elab_err("theorem apart(f: Nat → Nat, x, y: Nat, h: f(x) = f(y) + 1): False { omega }");
    assert!(msg.contains("got stuck"), "{msg}");
    assert!(msg.contains("f(x)") && msg.contains("f(y)"), "{msg}");
}

const SIGN: &str = "import bool;\n\
    fn sign(b: Bool) → int::Int { match b { False => int::NegSucc(0), True => int::OfNat(1) } }\n";

#[test]
fn a_closed_int_atom_is_its_numeral_on_either_side_of_zero() {
    ok(&format!(
        "{SIGN}theorem closed_int(x: int::Int, h: sign(True) + x = int::OfNat(0)): x = sign(False) {{ omega }}"
    ));
}

#[test]
fn an_int_argument_that_computes_meets_the_atom_it_computes_to() {
    ok("theorem int_side(g: List<Nat> → int::Int, h: g(list::List::append(Nil, Nil)) = g(Nil) + int::OfNat(1)): False { omega }");
}

#[test]
fn int_arguments_computing_to_different_values_stay_two_atoms() {
    let msg = elab_err(
        "theorem int_apart(g: List<Nat> → int::Int, h: g(Cons(0, Nil)) = g(list::List::append(Nil, Nil)) + int::OfNat(1)): False { omega }",
    );
    assert!(msg.contains("got stuck"), "{msg}");
    assert!(msg.contains("g(Cons(0, Nil))"), "{msg}");
}

#[test]
fn distinct_int_variables_stay_two_atoms() {
    let msg = elab_err("theorem int_vars(g: Nat → int::Int, x, y: Nat, h: g(x) = g(y) + int::OfNat(1)): False { omega }");
    assert!(msg.contains("got stuck"), "{msg}");
    assert!(msg.contains("g(x)") && msg.contains("g(y)"), "{msg}");
}
