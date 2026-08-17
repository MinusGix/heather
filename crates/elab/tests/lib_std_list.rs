//! `lib/std/list.hthr` — the list module's own closure, checked on its own.
//!
//! `tests/lib_list_algos.rs` already elaborates this file, but only on the way
//! to `lib/list_algos.hthr`, so a break in `std/list` was reported as the
//! algorithm file's problem. That mattered little when the module was three
//! functions; the L1/L2 waves (`issues/std-list-api.md`, 2026-08-17) made it
//! the library's second-largest, and it is now the thing under test rather
//! than a dependency of one.
//!
//! Two tests: the closure checks, and the L2 laws are actually *there*. The
//! second exists because a law that is deleted rather than broken is a change
//! the first test cannot see — the file would still check, with less in it.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
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

#[test]
fn the_list_module_checks() {
    elaborated();
}

/// The seven laws `issues/std-api-waves.md` named as wave L2, plus the three
/// this round proved on top of them. Named one by one rather than counted:
/// the point is which facts the library states, and a count would go on
/// passing while the wrong ten were present.
#[test]
fn the_law_kit_is_present() {
    let mut e = elaborated();
    let probe = r#"
import list;
import nat;
import bool;

theorem l_map_id<A>(xs: List<A>): map(xs, λ (a: A) => a) = xs { map_id(xs) }

theorem l_map_map<A, B, C>(xs: List<A>, f: A -> B, g: B -> C):
    map(map(xs, f), g) = map(xs, λ (a: A) => g(f(a)))
{ map_map(xs, f, g) }

theorem l_map_append<A, B>(xs, ys: List<A>, f: A -> B):
    map(append(xs, ys), f) = append(map(xs, f), map(ys, f))
{ map_append(xs, ys, f) }

theorem l_len_map<A, B>(xs: List<A>, f: A -> B): len(map(xs, f)) = len(xs) { len_map(xs, f) }

theorem l_len_append<A>(xs, ys: List<A>): len(append(xs, ys)) = add(len(xs), len(ys)) {
    len_append(xs, ys)
}

theorem l_rev_len<A>(xs: List<A>): len(rev(xs)) = len(xs) { rev_len(xs) }

theorem l_foldr_append<A, B>(xs, ys: List<A>, f: A -> B -> B, z: B):
    foldr(append(xs, ys), f, z) = foldr(xs, f, foldr(ys, f, z))
{ foldr_append(xs, ys, f, z) }

theorem l_len_replicate<A>(x: A, n: Nat): len(replicate(x, n)) = n { len_replicate(x, n) }

theorem l_take_drop<A>(xs: List<A>, n: Nat): append(take(xs, n), drop(xs, n)) = xs {
    take_append_drop(xs, n)
}

theorem l_len_filter<A>(xs: List<A>, p: A -> Bool): len(filter(xs, p)) <= len(xs) {
    len_filter(xs, p)
}
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the law kit did not apply: {msg}");
    }
}

/// The API *computes*, at closed arguments, by `refl` alone. The law test
/// above proves things about open lists and would pass over a `filter` that
/// kept everything or a `drop` that dropped nothing, since neither has a law
/// stated about it; these ten equations are what pins the programs.
///
/// `zip` is the one call here that spells its type arguments, and that is not
/// style: `B` occurs only in the curried tail, so it cannot be inferred
/// (`issues/curried-tail-type-arg-inference.md`). Written this way the test
/// keeps passing when that closes, and the issue's acceptance names the
/// unspelled form.
#[test]
fn the_api_computes() {
    let mut e = elaborated();
    let probe = r#"
import list;
import nat;
import bool;
import option;
import pair;

fn three() -> List<Nat> { Cons(1, Cons(2, Cons(3, Nil))) }

theorem c_len(): len(three()) = 3 { refl }
theorem c_take(): take(three(), 2) = Cons(1, Cons(2, Nil)) { refl }
theorem c_drop(): drop(three(), 2) = Cons(3, Nil) { refl }
theorem c_rev(): rev(three()) = Cons(3, Cons(2, Cons(1, Nil))) { refl }
theorem c_foldr(): foldr(three(), λ (a: Nat) (b: Nat) => add(a, b), 0) = 6 { refl }
theorem c_foldl(): foldl(three(), λ (a: Nat) (b: Nat) => add(a, b), 0) = 6 { refl }
theorem c_filter(): filter(three(), λ (n: Nat) => leb(2, n)) = Cons(2, Cons(3, Nil)) { refl }
theorem c_replicate(): replicate(7, 2) = Cons(7, Cons(7, Nil)) { refl }
theorem c_head(): three().head() = Some(1) { refl }
theorem c_last(): three().last() = Some(3) { refl }
theorem c_zip(): zip<Nat, Nat>(three(), Cons(4, Nil)) = Cons(Pair(1, 4), Nil) { refl }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the law kit did not apply: {msg}");
    }
}
