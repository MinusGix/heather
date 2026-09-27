//! Acceptance for issues/omega-atoms-up-to-computation.md: an atom that
//! computes to a numeral is that constant, and an atom that converts to one
//! already in the table is that atom, instead of each spelling being a
//! variable of its own. The positives are the issue's two one-liners (a
//! closed numeral under a global head; a local head over an argument that
//! computes), plus the same argument computing inside an **open** element
//! type and a closed atom met in a *checking* position. The controls pin what
//! computation must not merge: arguments that compute to different values
//! stay two atoms, and so do distinct variables.

use std::cell::OnceCell;
use std::sync::Mutex;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("omega", OMEGA),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn load_image() -> SemanticImage {
    // As in `omega_measure_reduction.rs`: one libtest worker fills the cold
    // image store, the others wait and replay it.
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    support::semantic_test_base(MODULES).semantic_image()
}

fn base() -> Elaborator {
    BASE.with(|base| base.get_or_init(load_image).elaborator())
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
