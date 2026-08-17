//! `lib/list_algos.hthr` — the list-algorithm exercise file
//! (`issues/list-algorithms-exercise.md`), checked as a module closure.
//!
//! Written when the traits adoption round (2026-08-07) moved `cong_cons`,
//! `append_nil` and `append_assoc` out of it and into `lib/std/list.hthr`, and
//! found that nothing in the suite would have noticed if the move had broken
//! the file: `lib/std/list.hthr`, `lib/std/option.hthr` and `lib/list_algos.hthr`
//! had no Rust coverage at all — only `nat` and `bool` did, through
//! `tests/ir_v1.rs`. The CLI's fixture tests exercise the *loader*, not these
//! files.
//!
//! One test, deliberately: the claim is that the closure checks, and the
//! interesting content (`rev_involutive`, insertion sort's sortedness proof)
//! is proof content that either checks or does not. Cheap — under a second of
//! the suite's budget.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGOS: &str = include_str!("../../../lib/list_algos.hthr");

#[test]
fn the_list_algorithms_check() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in
        [("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION), ("pair", PAIR), ("list", LIST), ("list_algos", ALGOS)]
    {
        if let Err(err) = e.elab_module_source(name, src) {
            let msg = match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            };
            panic!("{name} did not check: {msg}");
        }
    }
}

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("list_algos", ALGOS),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            let msg = match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            };
            panic!("{name} did not check: {msg}");
        }
    }
    e
}

/// Wave L3's permutation half (`issues/std-list-mem-and-perm.md`). The claim
/// this test defends is that the specification is now BOTH halves: `isort_correct`
/// is the conjunction, and it is cited here through its second field so that
/// deleting `count_isort` and leaving sortedness alone would fail.
#[test]
fn the_permutation_half_is_present() {
    let mut e = elaborated();
    let probe = r#"
import list_algos;
import list;
import nat;
import logic;

theorem p_count_insert(x: Nat, xs: List<Nat>, a: Nat):
    count(a, insert(x, xs)) = count(a, Cons(x, xs))
{ count_insert(x, xs, a) }

theorem p_count_isort(xs: List<Nat>, a: Nat): count(a, isort(xs)) = count(a, xs) {
    count_isort(xs, a)
}

theorem p_len_isort(xs: List<Nat>): len(isort(xs)) = len(xs) { len_isort(xs) }

theorem p_mem_isort(xs: List<Nat>, a: Nat, m: Mem(a, isort(xs))): Mem(a, xs) {
    mem_isort(xs, a, m)
}

theorem p_both(xs: List<Nat>, a: Nat):
    count(a, isort(xs)) = count(a, xs)
{ isort_correct(xs).right(a) }

theorem p_sorted(xs: List<Nat>): Sorted(isort(xs)) { isort_correct(xs).left }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the permutation half did not apply: {msg}");
    }
}

/// `count` and `isort` **compute**, and the negative control is what makes the
/// positive one mean something: a permutation statement proved only about open
/// lists would go on passing over a `count` that always answered `0`.
#[test]
fn sorting_and_counting_compute() {
    let mut e = elaborated();
    let probe = r#"
import list_algos;
import list;
import nat;

fn dup() -> List<Nat> { Cons(2, Cons(1, Cons(2, Nil))) }

theorem c_isort(): isort(dup()) = Cons(1, Cons(2, Cons(2, Nil))) { refl }
theorem c_count(): count(2, dup()) = 2 { refl }
theorem c_count_absent(): count(7, dup()) = 0 { refl }
theorem c_perm(): count(2, isort(dup())) = count(2, dup()) { refl }
theorem c_len(): len(isort(dup())) = 3 { refl }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the algorithms did not compute: {msg}");
    }

    // The control: `count` really counts multiplicity, so 2 occurrences is not 3.
    let mut e = elaborated();
    let bad = r#"
import list_algos;
import list;
import nat;

fn dup() -> List<Nat> { Cons(2, Cons(1, Cons(2, Nil))) }

theorem c_bad(): count(2, dup()) = 3 { refl }
"#;
    assert!(
        e.elab_module_source("bad", bad).is_err(),
        "count(2, [2,1,2]) = 3 was accepted, so `count` is not counting"
    );
}
