//! Acceptance for issues/omega-fact-arguments.md: `omega(e1, e2)` checks each
//! argument as a proof and reads its type as a fact, exactly as a `let` of it
//! would be read, for that call only. Rows: a call's fact about an atom omega
//! cannot see into, at `Nat` and at an open element type; several arguments
//! together at `Int`; a bare local; `omega(…)` in a checking position and as
//! a call's argument. The controls: the same goals with a bare `omega` are
//! refused, a listed fact does not reach a sibling `omega`, a non-proof
//! argument adds nothing, a named argument and an argument that does not
//! elaborate are refused.

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
    ("algebra", ALGEBRA),
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

// `bump` is stuck on its `Bool`, so omega reads `bump(b, n)` as an atom and
// knows nothing of it but what `bump_ge` states.
const PRELUDE: &str = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport int;\nimport omega;\n\
    fn bump(b: Bool, n: Nat) → Nat { match b { True => Succ(n), False => n } }\n\
    theorem bump_ge(b: Bool, n: Nat): n <= bump(b, n) {\n\
        match b { True => n.le_succ_r(n)(n.le_refl()), False => n.le_refl() }\n\
    }\n\
    fn ibump(b: Bool, x: Int) → Int { match b { True => x + OfNat(1), False => x } }\n\
    theorem ibump_ge(b: Bool, x: Int): x <= ibump(b, x) {\n\
        match b { True => { let k: (x <= x + OfNat(1)) = omega; k }, False => x.le_refl() }\n\
    }\n";

fn ok(src: &str) {
    let mut e = base();
    e.elab_module_source("m", &format!("{PRELUDE}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}"));
}

fn elab_err(src: &str) -> String {
    let mut e = base();
    match e.elab_module_source("m", &format!("{PRELUDE}{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

#[test]
fn a_call_argument_is_read_as_a_fact() {
    ok("theorem t(b: Bool, n: Nat): n < bump(b, n) + 1 { omega(bump_ge(b, n)) }");
    let msg = elab_err("theorem t(b: Bool, n: Nat): n < bump(b, n) + 1 { omega }");
    assert!(msg.contains("got stuck"), "{msg}");
}

#[test]
fn several_arguments_combine() {
    ok("theorem t(b, c: Bool, x: Int): x <= ibump(c, ibump(b, x)) {\n\
            omega(ibump_ge(b, x), ibump_ge(c, ibump(b, x)))\n\
        }");
    let msg = elab_err("theorem t(b, c: Bool, x: Int): x <= ibump(c, ibump(b, x)) {\n\
            omega(ibump_ge(b, x))\n\
        }");
    assert!(msg.contains("got stuck"), "{msg}");
}

#[test]
fn an_argument_at_an_open_element_type() {
    ok("theorem f<A>(xs: List<A>, p: A → Bool, n: Nat, h: xs.len() <= n): xs.filter(p).len() <= n {\n\
            omega(xs.len_filter(p))\n\
        }");
    let msg = elab_err("theorem f<A>(xs: List<A>, p: A → Bool, n: Nat, h: xs.len() <= n): xs.filter(p).len() <= n {\n\
            omega\n\
        }");
    assert!(msg.contains("got stuck"), "{msg}");
}

#[test]
fn a_bare_local_argument_is_the_fact_in_scope() {
    ok("theorem t(a, b: Nat, h: a < b): a + 1 <= b { omega(h) }");
    ok("theorem t(b: Bool, n: Nat): n < bump(b, n) + 1 {\n\
            let k = bump_ge(b, n);\n\
            omega(k)\n\
        }");
}

#[test]
fn an_argument_list_in_checking_positions() {
    ok("theorem t(b: Bool, n: Nat): n < bump(b, n) + 2 {\n\
            let k: (n < bump(b, n) + 1) = omega(bump_ge(b, n));\n\
            omega\n\
        }");
    ok("theorem t(b: Bool, n: Nat): Succ(n) <= Succ(bump(b, n)) {\n\
            n.le_succ_succ(bump(b, n), omega(bump_ge(b, n)))\n\
        }");
}

#[test]
fn a_listed_fact_does_not_reach_a_sibling_omega() {
    let msg = elab_err("theorem t(b: Bool, n: Nat): n <= bump(b, n) ∧ n < bump(b, n) + 1 {\n\
            And(omega(bump_ge(b, n)), omega)\n\
        }");
    assert!(msg.contains("got stuck"), "{msg}");
}

#[test]
fn a_non_proof_argument_adds_nothing() {
    let msg = elab_err("theorem t(b: Bool, n: Nat): n < bump(b, n) + 1 { omega(bump(b, n)) }");
    assert!(msg.contains("got stuck"), "{msg}");
}

#[test]
fn malformed_argument_lists_are_refused() {
    let msg = elab_err("theorem t(b: Bool, n: Nat): n < bump(b, n) + 1 { omega(h := bump_ge(b, n)) }");
    assert!(msg.contains("positionally"), "{msg}");
    let msg = elab_err("theorem t(b: Bool, n: Nat): n < bump(b, n) + 1 { omega(no_such_lemma(n)) }");
    assert!(msg.contains("no_such_lemma"), "{msg}");
}
