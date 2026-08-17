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

/// Wave L2′ (`issues/std-list-l2-prime-laws.md`): the laws L2 left out. Named
/// one by one for the same reason as above — these are the facts the library
/// now states about `foldl`, `filter` and `zip`, each of which had none.
///
/// Every `foldl` law is applied at an OPEN accumulator, which is the point:
/// they are stated `(z: B) -> …` because the accumulator varies with the
/// recursion, and a test that only used `0` would not see the difference.
#[test]
fn the_l2_prime_laws_are_present() {
    let mut e = elaborated();
    let probe = r#"
import list;
import nat;
import bool;
import pair;

theorem l_foldl_append<A, B>(xs, ys: List<A>, f: B -> A -> B, z: B):
    foldl(append(xs, ys), f, z) = foldl(ys, f, foldl(xs, f, z))
{ foldl_append(xs, ys, f, z) }

theorem l_foldl_rev<A, B>(xs: List<A>, f: B -> A -> B, z: B):
    foldl(rev(xs), f, z) = foldr(xs, λ (a: A) (b: B) => f(b, a), z)
{ foldl_rev(xs, f, z) }

theorem l_foldl_len<A>(xs: List<A>, z: Nat):
    foldl(xs, λ (k: Nat) (a: A) => Succ(k), z) = add(z, len(xs))
{ foldl_len(xs, z) }

theorem l_filter_append<A>(xs, ys: List<A>, p: A -> Bool):
    filter(append(xs, ys), p) = append(filter(xs, p), filter(ys, p))
{ filter_append(xs, ys, p) }

theorem l_filter_filter<A>(xs: List<A>, p: A -> Bool):
    filter(filter(xs, p), p) = filter(xs, p)
{ filter_filter(xs, p) }

theorem l_filter_map<A, B>(xs: List<A>, f: A -> B, p: B -> Bool):
    filter(map(xs, f), p) = map(filter(xs, λ (a: A) => p(f(a))), f)
{ filter_map(xs, f, p) }

theorem l_len_zip<A, B>(xs: List<A>, ys: List<B>):
    len(zip(xs, ys)) = min(len(xs), len(ys))
{ len_zip(xs, ys) }

theorem l_zip_map_fst<A, B>(xs: List<A>, ys: List<B>):
    map(zip(xs, ys), λ (q: Pair<A, B>) => q.fst) = take(xs, len(ys))
{ zip_map_fst(xs, ys) }

theorem l_zip_map_snd<A, B>(xs: List<A>, ys: List<B>):
    map(zip(xs, ys), λ (q: Pair<A, B>) => q.snd) = take(ys, len(xs))
{ zip_map_snd(xs, ys) }

theorem l_zip_swap<A, B>(xs: List<A>, ys: List<B>):
    map(zip(xs, ys), λ (q: Pair<A, B>) => swap(q)) = zip(ys, xs)
{ zip_swap(xs, ys) }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the L2' law kit did not apply: {msg}");
    }
}

/// Wave L3 (`issues/std-list-mem-and-perm.md`): `Mem` and its kit, at an
/// **open** element type — the axis `docs/testing-generated-terms.md` names
/// first, and the one that matters most here, since `Mem`'s whole claim is that
/// membership needs no decidable equality and so stays polymorphic.
///
/// The last two are the ones a closed type would hide: `Mem(a, Nil)` has to
/// *be* `False` (so refuting it is the hypothesis itself) and `mem_rev` has to
/// go through `mem_append` at an open `A`.
#[test]
fn the_mem_kit_is_present() {
    let mut e = elaborated();
    let probe = r#"
import list;
import logic;
import bool;

theorem m_head<A>(a: A, xs: List<A>): Mem(a, Cons(a, xs)) { mem_head(a, xs) }

theorem m_cons<A>(a, h: A, xs: List<A>, m: Mem(a, xs)): Mem(a, Cons(h, xs)) {
    mem_cons(a, h, xs, m)
}

theorem m_append_l<A>(xs, ys: List<A>, a: A, m: Mem(a, xs)): Mem(a, append(xs, ys)) {
    mem_append_l(xs, ys, a, m)
}

theorem m_append_r<A>(xs, ys: List<A>, a: A, m: Mem(a, ys)): Mem(a, append(xs, ys)) {
    mem_append_r(xs, ys, a, m)
}

theorem m_append<A>(xs, ys: List<A>, a: A, m: Mem(a, append(xs, ys))):
    Or<Mem(a, xs), Mem(a, ys)>
{ mem_append(xs, ys, a, m) }

theorem m_append_iff<A>(xs, ys: List<A>, a: A):
    Iff<Mem(a, append(xs, ys)), Or<Mem(a, xs), Mem(a, ys)>>
{ mem_append_iff(xs, ys, a) }

theorem m_map<A, B>(xs: List<A>, a: A, f: A -> B, m: Mem(a, xs)): Mem(f(a), map(xs, f)) {
    mem_map(xs, a, f, m)
}

theorem m_filter<A>(xs: List<A>, a: A, p: A -> Bool, m: Mem(a, filter(xs, p))): Mem(a, xs) {
    mem_filter(xs, a, p, m)
}

theorem m_not_nil<A>(a: A): ¬ Mem(a, Nil) { not_mem_nil(a) }

theorem m_rev<A>(xs: List<A>, a: A, m: Mem(a, rev(xs))): Mem(a, xs) { mem_rev(xs, a, m) }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the Mem kit did not apply: {msg}");
    }
}

/// The API *computes*, at closed arguments, by `refl` alone. The law test
/// above proves things about open lists and would pass over a `filter` that
/// kept everything or a `drop` that dropped nothing, since neither has a law
/// stated about it; these ten equations are what pins the programs.
///
/// `zip` is written unspelled since
/// `issues/curried-tail-type-arg-inference.md` closed: the over-applied second
/// list is what solves `B`. `crates/elab/tests/implicit_args.rs` owns the
/// inference itself, including the spelling that still needs its type
/// arguments.
#[test]
fn the_api_computes() {
    let mut e = elaborated();
    let probe = r#"
import list;
import nat;
import bool;
import option;
import pair;
import logic;

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
theorem c_zip(): zip(three(), Cons(4, Nil)) = Cons(Pair(1, 4), Nil) { refl }

// L2′/L3. `c_mem` is the one that says `Mem` is a *computing* relation and not
// a derivation to search: the proof is the position, written out.
theorem c_len_zip(): len(zip(three(), Cons(4, Nil))) = 1 { refl }
// `list::map` and not `map`: this probe imports `option` too, and a bare `map`
// with both in scope resolves to NEITHER — it reaches the prelude's vector `map`
// and fails asking for a vector. `issues/list-algorithms-exercise.md` predicted
// exactly this in 2026-08-05 and wave L2′ is its first real customer;
// `issues/type-owned-namespaces.md` owns the fix (`List::map`).
theorem c_zip_swap(): list::map(zip(three(), Cons(4, Nil)),
                                λ (q: Pair<Nat, Nat>) => swap(q))
    = zip(Cons(4, Nil), three()) { refl }
theorem c_filter_filter(): filter(filter(three(), λ (n: Nat) => leb(2, n)),
                                  λ (n: Nat) => leb(2, n)) = Cons(2, Cons(3, Nil)) { refl }
theorem c_foldl_rev(): foldl(rev(three()), λ (b: Nat) (a: Nat) => add(b, a), 0) = 6 { refl }
theorem c_mem(): Mem(2, three()) { Inr(Inl(refl)) }

// The negative control for `Mem`, and it is at `Bool` rather than at `Nat` on
// purpose: refuting `Mem` needs a DISEQUALITY of elements, `absurd` reads one
// only at a declared inductive, and `Nat` is the kernel's
// (`issues/absurd-at-nat-numerals.md` — at `Nat` this arm is three nested
// `succ_inj`s instead of one `absurd`). The list is still `List<Bool>`, so the
// `Mem` under test is the same polymorphic recursion.
theorem c_not_mem(): ¬ Mem(True, Cons(False, Nil)) {
    λ (m: Mem(True, Cons(False, Nil))) => match m {
        Inl(e) => absurd(e),
        Inr(bad) => bad,
    }
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
