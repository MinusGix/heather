//! A recursive `fn` means what its source means
//! (issues/fn-recursion-means-the-function.md).
//!
//! The structural lowering compiles the recursion at the `match`: a self-call
//! is the eliminator's hypothesis, i.e. *the `match` at the smaller value*,
//! and everything outside the `match` is evaluated once, by the top call. Each
//! shape below used to elaborate and compute a different value from its source
//! (`sum(2) = 4` by `refl` for a source that means 3). Now:
//!
//! - a recursive `match` that **reads its own parameter** (directly, or through
//!   a `let` or `have` bound from it above) is compiled by measure, which means
//!   the source, with a `recursion-by-measure` note, and refused with what to
//!   import where the measure route is not available;
//! - a recursive `match` **off the body's result**, or under a branch on its
//!   parameter, is refused at its recursive call. The measure route has no
//!   unfolding equation for those shapes (docs/decreases-unfolding-design.md §3).
//!
//! Every accepted case is pinned by what it *computes*, at a literal (`refl`)
//! and, for the fallback, through its unfolding equation at a symbolic one.

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, Lint, SemanticImage};

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

/// `termination_measures.rs`'s prefix, in its order, so the two share the
/// on-disk image the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", INT),
    ("omega", OMEGA),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const IMPORTS: &str = "import logic;\nimport nat;\nimport list;\nimport int;\nimport omega;\n";

const PLUS: &str =
    "fn plus(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(plus(a, k)) } }\n";

/// Check with the measure route available; return how many
/// `recursion-by-measure` notes the module raised.
fn ok(src: &str) -> usize {
    let mut e = base();
    e.elab_module_source("m", &format!("{IMPORTS}{PLUS}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}\n{src}"));
    e.take_warnings().iter().filter(|w| w.lint == Lint::RecursionByMeasure).count()
}

fn refused(src: &str, needle: &str) {
    let mut e = base();
    let msg = match e.elab_module_source("m", &format!("{IMPORTS}{PLUS}{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected a refusal:\n{src}"),
    };
    assert!(msg.contains(needle), "wrong refusal for\n{src}\n---\n{msg}");
    assert!(msg.contains("fn-recursion-means-the-function"), "{msg}");
}

// -- Reading the parameter: compiled by measure --------------------------------

#[test]
fn the_parameter_in_its_own_arm_is_compiled_by_measure() {
    let notes = ok("fn sum(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => plus(sum(k), n) } }
         theorem sum_2(): sum(2) = 3 { refl }
         theorem sum_step(k: Nat): sum(Succ(k)) = plus(sum(k), Succ(k)) { sum_unfold(Succ(k)) }");
    assert_eq!(notes, 1);
}

#[test]
fn every_way_of_reading_it_is_compiled_by_measure() {
    // The base arm runs at the bottom level, where `n` is zero.
    ok("fn z(n: Nat) -> Nat { match n { Zero => n, Succ(k) => z(k) } }
        theorem z_3(): z(3) = 0 { refl }");
    // Through a `let` and through a `have` bound above the `match`.
    ok("fn g(n: Nat) -> Nat { let m = n; match n { Zero => 0, Succ(k) => plus(g(k), m) } }
        theorem g_2(): g(2) = 3 { refl }");
    ok("fn g(n: Nat) -> Nat { have m = n; match n { Zero => 0, Succ(k) => plus(g(k), m) } }
        theorem g_2(): g(2) = 3 { refl }");
    // Two levels down, through the course-of-values chain.
    ok("fn h(n: Nat) -> Nat {
            match n { Zero => 0, Succ(k) => match k { Zero => 1, Succ(j) => plus(h(j), n) } }
        }
        theorem h_4(): h(4) = 6 { refl }");
    // A list, measured by its length, at an open element type.
    ok("fn w<A>(xs: List<A>) -> Nat { match xs { Nil => 0, Cons(_, t) => plus(w(t), xs.len()) } }
        theorem w_2(): w<Nat>([7, 8]) = 3 { refl }");
}

#[test]
fn without_the_measure_route_a_read_is_refused_with_what_to_import() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!(
        "{PLUS}fn sum(n: Nat) -> Nat {{ match n {{ Zero => 0, Succ(k) => plus(sum(k), n) }} }}"
    );
    let msg = match e.elab_source(&src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a refusal, got {other:?}"),
    };
    assert!(msg.contains("`n` is read inside its own recursive `match`"), "{msg}");
    assert!(msg.contains("import omega"), "{msg}");
}

#[test]
fn a_parameter_with_no_measure_is_refused() {
    refused(
        "inductive T { Leaf, Node(l: T, r: T) }
         fn leaves(t: T) -> Nat { match t { Leaf => 1, Node(l, r) => plus(leaves(l), leaves(t)) } }",
        "neither a `Nat` nor a `List`",
    );
}

// -- A value bound from a parameter the self-call varies ----------------------
//
// issues/recursion-let-reads-changing-parameter.md: the ih generalizes a
// parameter the self-call passes a different value (`count`'s `acc`), so the
// arms read *it* at this level; a `let` computed from it above the `match` is
// evaluated once, by the top call, and the structural lowering used to answer
// `u(1, x) = x + 1` by `refl`.

const U: &str = "fn u(n: Nat, x: Nat) -> Nat { let y = plus(x, 1); match n { Zero => y, Succ(k) => u(k, plus(x, 10)) } }\n";

#[test]
fn a_let_bound_from_a_varied_parameter_is_compiled_by_measure() {
    // Literal and neutral `x`, at a literal `n`; and the unfolding equation at
    // a neutral `n`, which is the self-call at the varied value.
    let notes = ok(&format!(
        "{U}theorem u_2(): u(2, 0) = 21 {{ refl }}
         theorem u_1_once(x: Nat): u(1, x) = plus(plus(x, 10), 1) {{ refl }}
         theorem u_step(k: Nat, x: Nat): u(Succ(k), x) = u(k, plus(x, 10)) {{ u_unfold(Succ(k), x) }}"
    ));
    assert_eq!(notes, 1);
}

#[test]
fn the_top_calls_value_is_refused() {
    // The negative control: what the structural lowering used to compute.
    let mut e = base();
    support::assert_refused(
        &mut e,
        "m",
        &format!("{IMPORTS}{PLUS}{U}theorem wrong(x: Nat): u(1, x) = plus(x, 1) {{ refl }}"),
        support::Refusal::Kernel,
    );
}

#[test]
fn every_way_of_reading_a_varied_value_is_compiled_by_measure() {
    // Through a `have`, in a checking position.
    ok("fn h(n: Nat, x: Nat) -> Nat { have y: Nat = plus(x, 1); match n { Zero => y, Succ(k) => h(k, plus(x, 10)) } }
        theorem h_1(): h(1, 0) = 11 { refl }");
    // In the self-call's own argument: each level passes its own `y` on.
    ok("fn a(n: Nat, x: Nat) -> Nat { let y = plus(x, 1); match n { Zero => x, Succ(k) => a(k, y) } }
        theorem a_2(): a(2, 0) = 2 { refl }");
    // Through a chain of `let`s, read under a nested `match` in an arm.
    ok("fn c(n: Nat, x: Nat) -> Nat {
            let y = plus(x, 1); let z = plus(y, y);
            match n { Zero => 0, Succ(k) => match k { Zero => z, Succ(_) => c(k, plus(x, 1)) } }
        }
        theorem c_2(): c(2, 0) = 4 { refl }");
    // A list recursion with an open element type, varying an accumulator.
    ok("fn r<A>(xs: List<A>, acc: List<A>) -> Nat {
            let l = acc.len();
            match xs { Nil => l, Cons(h, t) => r(t, Cons(h, acc)) }
        }
        theorem r_2(): r<Nat>([7, 8], []) = 2 { refl }");
}

#[test]
fn a_varied_value_at_a_parameter_with_no_measure_is_refused() {
    refused(
        "inductive T { Leaf, Node(l: T, r: T) }
         fn d(t: T, x: Nat) -> Nat { let y = plus(x, 1); match t { Leaf => y, Node(l, r) => d(l, plus(x, 1)) } }",
        "bind `y` inside each arm that reads it",
    );
}

#[test]
fn reading_the_varied_parameter_itself_keeps_the_structural_lowering() {
    // The ih's generalized binder is this level's value, and so is a `let`
    // bound from it inside the arm, or from a parameter passed unchanged.
    let notes = ok("fn u(n: Nat, x: Nat) -> Nat { match n { Zero => plus(x, 1), Succ(k) => u(k, plus(x, 10)) } }
         theorem u_2(): u(2, 0) = 21 { refl }
         theorem u_step(k: Nat, x: Nat): u(Succ(k), x) = u(k, plus(x, 10)) { refl }
         fn v(n: Nat, x: Nat) -> Nat { match n { Zero => { let y = plus(x, 1); y }, Succ(k) => v(k, plus(x, 10)) } }
         theorem v_2(): v(2, 0) = 21 { refl }
         fn w(n: Nat, x: Nat, b: Nat) -> Nat { let y = plus(b, 1); match n { Zero => plus(x, y), Succ(k) => w(k, plus(x, 10), b) } }
         theorem w_2(): w(2, 0, 0) = 21 { refl }");
    assert_eq!(notes, 0);
}

// -- The recursive `match` off the result: refused -----------------------------

#[test]
fn a_recursive_match_off_the_result_is_refused() {
    refused(
        "fn f(n: Nat) -> Nat { plus(1, match n { Zero => 0, Succ(k) => f(k) }) }",
        "is not the result of `f`",
    );
    refused(
        "fn e(n: Nat) -> Nat { plus(match n { Zero => 0, Succ(k) => e(k) }, n) }",
        "is not the result of `e`",
    );
    refused(
        "fn l(n: Nat) -> Nat { let r: Nat = match n { Zero => 0, Succ(k) => l(k) }; plus(r, 1) }",
        "is not the result of `l`",
    );
    refused(
        "fn v(xs: List<Nat>) -> Nat { Succ(match xs { Nil => 0, Cons(_, t) => v(t) }) }",
        "is not the result of `v`",
    );
}

#[test]
fn a_recursive_match_under_a_branch_on_its_parameter_is_refused() {
    refused(
        "inductive B { T, F }
         fn is_zero(n: Nat) -> B { match n { Zero => T, Succ(_) => F } }
         fn f(n: Nat) -> Nat { match is_zero(n) { T => 7, F => match n { Zero => 0, Succ(k) => f(k) } } }",
        "sits under a branch that depends on `n`",
    );
}

// -- What keeps the structural lowering ----------------------------------------

#[test]
fn the_structural_spellings_keep_definitional_unfolding() {
    let notes = ok("fn tri(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => plus(tri(k), Succ(k)) } }
         theorem tri_2(): tri(2) = 3 { refl }
         theorem tri_step(k: Nat): tri(Succ(k)) = plus(tri(k), Succ(k)) { refl }
         fn g(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => { have m = Succ(k); plus(g(k), m) } } }
         theorem g_2(): g(2) = 3 { refl }");
    assert_eq!(notes, 0);
}

#[test]
fn unchanged_and_varying_parameters_are_not_the_recursion() {
    let notes = ok("inductive B { T, F }
         fn pick(n: Nat, b: B) -> Nat {
             match n { Zero => 0, Succ(k) => match b { T => Succ(pick(k, b)), F => pick(k, b) } }
         }
         theorem pick_t(): pick(2, T) = 2 { refl }
         fn count(n: Nat, acc: Nat) -> Nat { match n { Zero => acc, Succ(k) => count(k, plus(acc, 1)) } }
         theorem count_2(): count(2, 5) = 7 { refl }");
    assert_eq!(notes, 0);
}

/// A dot call on another type's member of the same name is not a self-call,
/// which the syntax cannot see and the elaborator can: an off-result `match`
/// whose only "self-call" is one of those is not refused.
#[test]
fn another_types_member_is_not_mistaken_for_the_recursion() {
    ok("inductive Box<A> { Mk(contents: List<A>) }
        fn Box::len<A>(self b: Box<A>) -> Nat { plus(1, match b { Mk(c) => c.len() }) }
        theorem box_len(): Mk<Nat>([1, 2]).len() = 3 { refl }");
}

#[test]
fn non_recursive_matches_and_theorems_are_untouched() {
    let notes = ok("fn once(n: Nat) -> Nat { plus(1, match n { Zero => n, Succ(_) => n }) }
         theorem walk(n: Nat): True {
             match n { Zero => trivial, Succ(k) => { let r = walk(k); let q: (n = n) = refl; trivial } }
         }");
    assert_eq!(notes, 0);
}
