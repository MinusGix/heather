//! `lib/std/bounded_list.hthr` — capacity-bounded lists, their stack API, and
//! the first ordinary client of propositional truncation.

mod support;
use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const BOUNDED_LIST: &str = include_str!("../../../lib/std/bounded_list.hthr");

fn elaborated() -> Elaborator {
    let mut e = support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("bounded_list", BOUNDED_LIST),
    ]);
    e
}

#[test]
fn the_bounded_list_module_checks() {
    elaborated();
}

#[test]
fn squash_combinators_and_stack_laws_apply_at_open_inputs() {
    let mut e = elaborated();
    let probe = r#"
import logic;
import nat;
import list;
import pair;
import bounded_list;

theorem map_beta<A, B>(a: A, f: A -> B):
    squash_map(squash(a), f) = squash(f(a))
{ squash_map_intro(a, f) }

theorem bind_assoc<A, B, C>(q: ∥A∥, f: A -> ∥B∥, g: B -> ∥C∥):
    squash_bind<B, C>(squash_bind<A, B>(q, f), g) =
        squash_bind<A, C>(q, λ (x: A) => squash_bind<B, C>(f(x), g))
{ squash_bind_assoc(q, f, g) }

theorem lifo<A>(x: A, xs: BoundedList<A>,
    h: Succ(xs.len()) <= capacity(xs)):
    run(Cons(Push(x), Cons(Pop, Nil)), xs) = Success(xs)
{ run_push_pop(x, xs, h) }

theorem receiver_len<A>(xs: BoundedList<A>):
    xs.len() = bounded_len(xs)
{ refl }

theorem rejected<A>(x: A, xs: BoundedList<A>,
    h: ¬(Succ(xs.len()) <= capacity(xs))):
    push(x, xs) = Overflow(xs)
{ push_overflow(x, xs, h) }

theorem pushed_len<A>(x: A, xs: BoundedList<A>,
    h: Succ(xs.len()) <= capacity(xs)):
    BoundedList<A>(capacity := capacity(xs),
        contents := Cons(x, xs.contents), fit := squash(h)).len() =
        Succ(xs.len())
{ len_after_push(x, xs, h) }

theorem popped_capacity<A>(limit: Nat, tail: List<A>,
    fit: ∥Succ(tail.len()) <= limit∥):
    capacity(bounded_tail(limit, tail, fit)) = limit
{ capacity_after_pop(limit, tail, fit) }

theorem sequences<A>(a, b: List<StackOp<A>>, xs: BoundedList<A>):
    run(a ++ b, xs) = match run(a, xs) {
        Success(next) => run(b, next),
        Underflow(same) => Underflow(same),
        Overflow(same) => Overflow(same),
    }
{ run_append(a, b, xs) }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("open bounded-list laws did not apply: {msg}");
    }
}

#[test]
fn closed_success_underflow_and_overflow_compute() {
    let mut e = elaborated();
    let probe = r#"
import bounded_list;
import list;

theorem empty_underflows(): pop(empty<Nat>(2)) = Underflow(empty<Nat>(2)) { refl }
theorem one_push_runs():
    run(Cons(Push(7), Nil), empty<Nat>(1)) =
        Success(BoundedList(capacity := 1, contents := Cons(7, Nil), fit := squash(trivial)))
{ refl }
theorem second_push_overflows():
    run(Cons(Push(7), Cons(Push(8), Nil)), empty<Nat>(1)) =
        Overflow(BoundedList(capacity := 1, contents := Cons(7, Nil), fit := squash(trivial)))
{ refl }
"#;
    if let Err(err) = e.elab_module_source("closed", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("closed bounded-list computations failed: {msg}");
    }
}

#[test]
fn an_invalid_fit_witness_is_rejected() {
    let mut e = elaborated();
    let bad = r#"
import bounded_list;
import list;
fn impossible() -> BoundedList<Nat> {
    BoundedList(capacity := 0, contents := Cons(1, Nil), fit := squash(trivial))
}
"#;
    assert!(e.elab_module_source("bad", bad).is_err(), "an overflowing value was constructed");
}
