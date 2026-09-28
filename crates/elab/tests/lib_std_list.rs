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

use crate::support;
use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");

fn elaborated() -> Elaborator {
    let mut e = support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
    ]);
    e
}

#[test]
fn the_list_module_checks() {
    elaborated();
}

#[test]
fn its_literal_instance_uses_the_compact_protocol_lowering() {
    let mut e = elaborated();
    let before = e.psi().bindings.len();
    e.elab_module_source("list_literal_probe", "import list; fn xs() -> List<Nat> { [1, 2] }")
        .expect("literal checks");
    assert_eq!(e.psi().bindings.len(), before + 1);
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

theorem l_map_id<A>(xs: List<A>): xs.map(λ (a: A) => a) = xs { xs.map_id() }

theorem l_map_map<A, B, C>(xs: List<A>, f: A -> B, g: B -> C):
    xs.map(f).map(g) = xs.map(λ (a: A) => g(f(a)))
{ xs.map_map(f, g) }

theorem l_map_append<A, B>(xs, ys: List<A>, f: A -> B):
    xs.append(ys).map(f) = xs.map(f).append(ys.map(f))
{ xs.map_append(ys, f) }

theorem l_len_map<A, B>(xs: List<A>, f: A -> B): xs.map(f).len() = xs.len() { xs.len_map(f) }

theorem l_len_append<A>(xs, ys: List<A>):
    xs.append(ys).len() = xs.len().add(ys.len()) {
    xs.len_append(ys)
}

theorem l_rev_len<A>(xs: List<A>): xs.rev().len() = xs.len() { xs.rev_len() }

theorem l_foldr_append<A, B>(xs, ys: List<A>, f: A -> B -> B, z: B):
    xs.append(ys).foldr(f, z) = xs.foldr(f, ys.foldr(f, z))
{ xs.foldr_append(ys, f, z) }

theorem l_len_replicate<A>(x: A, n: Nat): List::replicate(x, n).len() = n { List::len_replicate(x, n) }

theorem l_take_drop<A>(xs: List<A>, n: Nat): xs.take(n).append(xs.drop(n)) = xs {
    xs.take_append_drop(n)
}

theorem l_len_filter<A>(xs: List<A>, p: A -> Bool): xs.filter(p).len() <= xs.len() {
    xs.len_filter(p)
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
    xs.append(ys).foldl(f, z) = ys.foldl(f, xs.foldl(f, z))
{ xs.foldl_append(ys, f, z) }

theorem l_foldl_rev<A, B>(xs: List<A>, f: B -> A -> B, z: B):
    xs.rev().foldl(f, z) = xs.foldr(λ (a: A) (b: B) => f(b, a), z)
{ xs.foldl_rev(f, z) }

theorem l_foldl_len<A>(xs: List<A>, z: Nat):
    xs.foldl(λ (k: Nat) (a: A) => Succ(k), z) = z.add(xs.len())
{ xs.foldl_len(z) }

theorem l_filter_append<A>(xs, ys: List<A>, p: A -> Bool):
    xs.append(ys).filter(p) = xs.filter(p).append(ys.filter(p))
{ xs.filter_append(ys, p) }

theorem l_filter_filter<A>(xs: List<A>, p: A -> Bool):
    xs.filter(p).filter(p) = xs.filter(p)
{ xs.filter_filter(p) }

theorem l_filter_map<A, B>(xs: List<A>, f: A -> B, p: B -> Bool):
    xs.map(f).filter(p) = xs.filter(λ (a: A) => p(f(a))).map(f)
{ xs.filter_map(f, p) }

theorem l_len_zip<A, B>(xs: List<A>, ys: List<B>):
    xs.zip(ys).len() = xs.len().min(ys.len())
{ xs.len_zip(ys) }

theorem l_zip_map_fst<A, B>(xs: List<A>, ys: List<B>):
    xs.zip(ys).map(λ (q: Pair<A, B>) => q.fst) = xs.take(ys.len())
{ xs.zip_map_fst(ys) }

theorem l_zip_map_snd<A, B>(xs: List<A>, ys: List<B>):
    xs.zip(ys).map(λ (q: Pair<A, B>) => q.snd) = ys.take(xs.len())
{ xs.zip_map_snd(ys) }

theorem l_zip_swap<A, B>(xs: List<A>, ys: List<B>):
    xs.zip(ys).map(Pair::swap) = ys.zip(xs)
{ xs.zip_swap(ys) }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the L2' law kit did not apply: {msg}");
    }
}

/// The concrete first-class algebra experiment
/// (`issues/datatype-container-algebras.md`). This is deliberately more than
/// a constructor-equation check: uniqueness is consumed at an arbitrary
/// function, and fusion crosses three open carriers at a neutral list.
#[test]
fn the_first_class_algebra_laws_are_present() {
    let mut e = elaborated();
    let probe = r#"
import list;

theorem a_nil<A, B>(alg: ListAlg<A, B>): alg.list_fold(Nil) = alg.nil {
    alg.list_fold_nil()
}

theorem a_cons<A, B>(alg: ListAlg<A, B>, h: A, t: List<A>):
    alg.list_fold(Cons(h, t)) = alg.cons(h, alg.list_fold(t))
{ alg.list_fold_cons(h, t) }

theorem a_unique<A, B>(alg: ListAlg<A, B>, g: List<A> -> B,
    nil_law: g(Nil) = alg.nil,
    cons_law: (h: A) -> (t: List<A>) -> g(Cons(h, t)) = alg.cons(h, g(t)),
    xs: List<A>): g(xs) = alg.list_fold(xs)
{ alg.list_fold_unique(g, nil_law, cons_law, xs) }

theorem a_fusion<A, B, C>(src: ListAlg<A, B>, dst: ListAlg<A, C>,
    hom: B -> C,
    nil_comm: hom(src.nil) = dst.nil,
    cons_comm: (a: A) -> (b: B) -> hom(src.cons(a, b)) = dst.cons(a, hom(b)),
    xs: List<A>): hom(src.list_fold(xs)) = dst.list_fold(xs)
{ src.list_fold_fusion(dst, hom, nil_comm, cons_comm, xs) }

theorem a_foldr<A, B>(f: A -> B -> B, z: B, xs: List<A>):
    (ListAlg<A, B> { nil: z, cons: f }).list_fold(xs) = xs.foldr(f, z)
{ ListAlg::list_fold_is_foldr(f, z, xs) }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the algebra kit did not apply: {msg}");
    }
}

/// The motive itself is open here: this is the higher-kinded record parameter
/// that the old case-algebra sketch listed as missing, not one monomorphic
/// equality chosen by the test.
#[test]
fn the_dependent_elimination_algebra_is_first_class() {
    let mut e = elaborated();
    let probe = r#"
import list;

theorem e_use<A>(P: List<A> -> Type, alg: ListElim<A>(P), xs: List<A>): P(xs) {
    List::list_elim(P, alg, xs)
}

theorem e_nil<A>(P: List<A> -> Type, alg: ListElim<A>(P)):
    List::list_elim(P, alg, Nil) = alg.nil
{ List::list_elim_nil(P, alg) }

theorem e_cons<A>(P: List<A> -> Type, alg: ListElim<A>(P), h: A, t: List<A>):
    List::list_elim(P, alg, Cons(h, t)) = alg.cons(h, t, List::list_elim(P, alg, t))
{ List::list_elim_cons(P, alg, h, t) }

theorem e_append_nil<A>(xs: List<A>): xs.append(Nil) = xs { xs.append_nil() }
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("the dependent algebra did not apply: {msg}");
    }
}

#[test]
fn a_wrong_list_obligation_is_rejected() {
    let mut e = elaborated();
    let bad = r#"
import list;

fn bad_append_nil<A>() -> ListElim<A>(λ (xs: List<A>) => xs.append(Nil) = xs) {
    ListElim {
        nil: refl,
        // `ih` proves the property at `tail`, not at `Cons(head, tail)`.
        cons: λ (head: A) (tail: List<A>) ih => ih,
    }
}
"#;
    assert!(e.elab_module_source("bad", bad).is_err(), "the wrong Cons obligation checked");
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
    xs.mem_cons(a, h, m)
}

theorem m_append_l<A>(xs, ys: List<A>, a: A, m: Mem(a, xs)): Mem(a, xs.append(ys)) {
    xs.mem_append_l(ys, a, m)
}

theorem m_append_r<A>(xs, ys: List<A>, a: A, m: Mem(a, ys)): Mem(a, xs.append(ys)) {
    xs.mem_append_r(ys, a, m)
}

theorem m_append<A>(xs, ys: List<A>, a: A, m: Mem(a, xs.append(ys))):
    Or<Mem(a, xs), Mem(a, ys)>
{ xs.mem_append(ys, a, m) }

theorem m_append_iff<A>(xs, ys: List<A>, a: A):
    Iff<Mem(a, xs.append(ys)), Or<Mem(a, xs), Mem(a, ys)>>
{ xs.mem_append_iff(ys, a) }

theorem m_map<A, B>(xs: List<A>, a: A, f: A -> B, m: Mem(a, xs)): Mem(f(a), xs.map(f)) {
    xs.mem_map(a, f, m)
}

theorem m_filter<A>(xs: List<A>, a: A, p: A -> Bool, m: Mem(a, xs.filter(p))): Mem(a, xs) {
    xs.mem_filter(a, p, m)
}

theorem m_not_nil<A>(a: A): ¬ Mem(a, Nil) { not_mem_nil(a) }

theorem m_rev<A>(xs: List<A>, a: A, m: Mem(a, xs.rev())): Mem(a, xs) { xs.mem_rev(a, m) }
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

theorem c_len(): three().len() = 3 { refl }
theorem c_take(): three().take(2) = Cons(1, Cons(2, Nil)) { refl }
theorem c_drop(): three().drop(2) = Cons(3, Nil) { refl }
theorem c_rev(): three().rev() = Cons(3, Cons(2, Cons(1, Nil))) { refl }
theorem c_foldr(): three().foldr(λ (a: Nat) (b: Nat) => a.add(b), 0) = 6 { refl }
theorem c_foldl(): three().foldl(λ (a: Nat) (b: Nat) => a.add(b), 0) = 6 { refl }
theorem c_list_fold():
    (ListAlg<Nat, Nat> { nil: 0, cons: λ (a: Nat) (b: Nat) => a.add(b) }).list_fold(three()) = 6
{ refl }
theorem c_filter(): three().filter(λ (n: Nat) => nat::Nat::leb(2, n)) = Cons(2, Cons(3, Nil)) { refl }
theorem c_replicate(): List::replicate(7, 2) = Cons(7, Cons(7, Nil)) { refl }
theorem c_head(): three().head() = Some(1) { refl }
theorem c_last(): three().last() = Some(3) { refl }
theorem c_receiver_len(): three().len() = 3 { refl }
theorem c_zip(): three().zip(Cons(4, Nil)) = Cons(Pair(1, 4), Nil) { refl }

theorem receiver_len_open<A>(xs: List<A>): xs.len() = xs.len() { refl }

// L2′/L3. `c_mem` is the one that says `Mem` is a *computing* relation and not
// a derivation to search: the proof is the position, written out.
theorem c_len_zip(): three().zip(Cons(4, Nil)).len() = 1 { refl }
// `list::List::map` and not `map`: this probe imports `option` too, and a bare `map`
// with both in scope resolves to NEITHER — it reaches the prelude's vector `map`
// and fails asking for a vector. `issues/list-algorithms-exercise.md` predicted
// exactly this in 2026-08-05 and wave L2′ is its first real customer;
// `issues/type-owned-namespaces.md` owns the fix (`List::map`).
theorem c_zip_swap(): list::List::map(three().zip(Cons(4, Nil)),
                                Pair::swap)
    = Cons(4, Nil).zip(three()) { refl }
theorem c_filter_filter(): three().filter(λ (n: Nat) => nat::Nat::leb(2, n)).filter(
                                  λ (n: Nat) => nat::Nat::leb(2, n)) = Cons(2, Cons(3, Nil)) { refl }
theorem c_foldl_rev(): three().rev().foldl(λ (b: Nat) (a: Nat) => b.add(a), 0) = 6 { refl }
theorem c_mem(): Mem(2, three()) { Inr(Inl(refl)) }

// The negative control for `Mem` can now use kernel Nat directly: `absurd`
// peels matching Succ layers internally until each equation exposes the
// Zero/Succ mismatch (`issues/absurd-at-nat-numerals.md`).
theorem c_not_mem(): ¬ Mem(7, Cons(1, Cons(2, Nil))) {
    λ (m: Mem(7, Cons(1, Cons(2, Nil)))) => match m {
        Inl(e) => absurd(e),
        Inr(Inl(e)) => absurd(e),
        Inr(Inr(bad)) => bad,
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

/// Decidable equality, the generic one: `logic::DecEq<A>` is the premise and
/// `list_eq_dec` the decision, so a list decides exactly when its element type
/// does. Shaped by `docs/testing-generated-terms.md` — a literal *and* a
/// neutral list, a checking position, and a negative control — because a
/// closed scrutinee alone would not see whether the decider is stuck at open
/// endpoints or merely wrong there.
///
/// The `Decide<xs = ys>` bridge is at `List<Nat>` and not at an open element
/// type: see the note in `lib/std/list.hthr` and
/// `issues/instance-binder-occurrence-through-binder-types.md`.
#[test]
fn list_equality_decides_at_a_literal_and_resolves_at_open_endpoints() {
    let mut e = elaborated();
    let probe = r#"
import list;
import nat;
import logic;

fn three() -> List<Nat> { Cons(1, Cons(2, Cons(3, Nil))) }
fn other() -> List<Nat> { Cons(1, Cons(2, Cons(4, Nil))) }

// Closed: the decision runs, both ways round, in a checking position.
theorem agree(): three() = three() { decide }
theorem differ(): ¬(three() = other()) { decide }
theorem shorter(): ¬(three() = Cons(1, Nil)) { decide }
theorem empty_differs(): ¬(Nil<Nat> = Cons(1, Nil)) { decide }

// Neutral: the instance is the declared decider at open endpoints, which is
// what a literal-only test cannot see.
theorem neutral_instance(xs, ys: List<Nat>, a, b: Nat):
    decide_pick<xs = ys, Nat>(a, b) = or_pick(xs.list_eq_dec(ys), a, b) { refl }

// The element decision is the class's, at an OPEN element type: this is the
// half that makes the decider generic rather than a second `Nat` program.
// A `Cons` is never `Nil`, at an open element type and by computation: the
// decider reduces past the element decision it never has to make.
theorem open_element<A: DecEq>(x: A, xs: List<A>, a, b: A):
    or_pick(Cons(x, xs).list_eq_dec(Nil<A>), a, b) = a { refl }
theorem open_cons_head<A: DecEq>(x: A, xs: List<A>): ¬(Nil<A> = Cons(x, xs)) {
    List::nil_ne_cons(xs, x)
}
"#;
    if let Err(err) = e.elab_module_source("probe", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("list equality did not decide: {msg}");
    }
    // The negative control: `decide` cannot prove a false equation, and cannot
    // prove one whose endpoints it has no closed decision for.
    for bad in [
        "theorem bad(): Cons(1, Nil) = Cons(2, Nil) { decide }\n",
        "theorem bad(xs: List<Nat>): xs = Cons(1, Nil) { decide }\n",
    ] {
        let src = format!("import list;\nimport nat;\nimport logic;\n{bad}");
        let mut e = elaborated();
        assert!(
            e.elab_module_source("bad_probe", &src).is_err(),
            "accepted: {bad}"
        );
    }
}
