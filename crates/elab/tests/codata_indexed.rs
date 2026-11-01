//! Acceptance for **indexed** `codata` (`docs/codata-indexed-design.md`,
//! `issues/codata-indexed.md`): the index binders are in scope in the field
//! types, a child writes its own index, and the lowering is the kernel's
//! indexed `M`. On the four axes of `docs/testing-generated-terms.md`:
//! literal *and* neutral indices and scrutinees, an open element type,
//! checking positions, and a negative control for every rule.
//!
//! Every declaration is re-checked by the real kernel, so a wrong encoding is
//! a rejection; the `refl` theorems are what catch a well-typed wrong one —
//! each is an observation `out`'s β rule must compute, through the `J` that
//! moves a corecursive step to its index (§6).

use heather_elab::{ElabError, Elaborator};

use crate::support;

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

const STREAM: &str = r#"
codata Stream { SCons(head: Nat, tail: Stream) }
fn hd(s: Stream) -> Nat { match s { SCons(h, _) => h } }
fn tl(s: Stream) -> Stream { match s { SCons(_, t) => t } }
fn zeros() -> Stream { SCons(0, zeros()) }
fn from(n: Nat) -> Stream { SCons(n, from(Succ(n))) }
codata SBisim : (s: Stream) -> (t: Stream) -> Type {
    Same(heads: hd(s) = hd(t), tails: SBisim(tl(s), tl(t))),
}
fn heads(s: Stream, t: Stream, b: SBisim(s, t)) -> hd(s) = hd(t) { match b { Same(h, _) => h } }
fn tails(s: Stream, t: Stream, b: SBisim(s, t)) -> SBisim(tl(s), tl(t)) { match b { Same(_, k) => k } }
fn sb_refl(s: Stream) -> SBisim(s, s) { Same(refl, sb_refl(tl(s))) }
"#;

// §2–§4: the declaration lowers, a constructor checks its payload at the
// index (`hd(s) = hd(s)` by `refl`) and its child at the written index, and
// `match` hands both back.
#[test]
fn constructors_at_an_index() {
    elab(&format!(
        "{STREAM}
         fn same_here(s: Stream, b: SBisim(tl(s), tl(s))) -> SBisim(s, s) {{ Same(refl, b) }}
         theorem tails_here(s: Stream, b: SBisim(tl(s), tl(s))): tails(s, s, same_here(s, b)) = b {{ refl }}
         fn zero_heads() -> hd(zeros()) = hd(zeros()) {{ heads(zeros(), zeros(), sb_refl(zeros())) }}"
    ));
}

// §6: coinduction proper. `sb_refl`'s carrier is `Σ s. Id(⟨s, s⟩; i)`, and
// one `out` gives the next step at the child's index, by `J` at `refl`: at a
// neutral stream and a literal one.
#[test]
fn corecursion_at_a_varying_index() {
    elab(&format!(
        "{STREAM}
         theorem refl_tails(s: Stream): tails(s, s, sb_refl(s)) = sb_refl(tl(s)) {{ refl }}
         theorem refl_heads(s: Stream): heads(s, s, sb_refl(s)) = refl {{ refl }}
         theorem refl_from(): tails(from(0), from(0), sb_refl(from(0))) = sb_refl(from(1)) {{ refl }}"
    ));
}

// §6: a corecursive argument that is itself indexed codata (`b`), and a
// result index that swaps or composes the parameters: symmetry and
// transitivity, with `match` in step position.
#[test]
fn symmetry_and_transitivity() {
    elab(&format!(
        "{STREAM}
         fn sb_sym(s: Stream, t: Stream, b: SBisim(s, t)) -> SBisim(t, s) {{
             match b {{ Same(h, k) => Same(sym(h), sb_sym(tl(s), tl(t), k)) }}
         }}
         fn sb_trans(s: Stream, t: Stream, u: Stream, a: SBisim(s, t), b: SBisim(t, u)) -> SBisim(s, u) {{
             match a {{ Same(h1, k1) => match b {{ Same(h2, k2) => Same(trans(h1, h2), sb_trans(tl(s), tl(t), tl(u), k1, k2)) }} }}
         }}
         theorem sym_tails(s: Stream): tails(s, s, sb_sym(s, s, sb_refl(s))) = sb_sym(tl(s), tl(s), sb_refl(tl(s))) {{ refl }}"
    ));
}

// An index that is an inductive value, with the equation a field: literal
// and neutral observations through two steps.
#[test]
fn nat_index_with_an_equation_field() {
    elab(
        "codata Count : (n: Nat) -> Type { Tick(at: Nat, ok: at = n, next: Count(Succ(n))) }
         fn here(n: Nat, c: Count(n)) -> Nat { match c { Tick(a, _, _) => a } }
         fn later(n: Nat, c: Count(n)) -> Count(Succ(n)) { match c { Tick(_, _, k) => k } }
         fn count(n: Nat) -> Count(n) { Tick(n, refl, count(Succ(n))) }
         theorem lit(): here(3, later(2, count(2))) = 3 { refl }
         theorem open(n: Nat): here(Succ(Succ(n)), later(Succ(n), later(n, count(n)))) = Succ(Succ(n)) { refl }",
    );
}

// The open element type: bisimilarity over `Seq<A>`, a type parameter on the
// declaration and on the corecursive proof.
#[test]
fn open_element_type() {
    elab(
        "codata Seq<A> { Cons(h: A, t: Seq<A>) }
         fn shd<A>(s: Seq<A>) -> A { match s { Cons(h, _) => h } }
         fn stl<A>(s: Seq<A>) -> Seq<A> { match s { Cons(_, t) => t } }
         codata Bis<A> : (s: Seq<A>) -> (t: Seq<A>) -> Type {
             Both(h: shd(s) = shd(t), k: Bis<A>(stl(s), stl(t))),
         }
         fn bis_k<A>(s: Seq<A>, t: Seq<A>, b: Bis<A>(s, t)) -> Bis<A>(stl(s), stl(t)) { match b { Both(_, k) => k } }
         fn bis_refl<A>(s: Seq<A>) -> Bis<A>(s, s) { Both(refl, bis_refl(stl(s))) }
         theorem bis_step<A>(s: Seq<A>): bis_k(s, s, bis_refl(s)) = bis_refl(stl(s)) { refl }",
    );
}

// A function child whose domain mentions the index, a λ in child position,
// an existing function child passed whole (η-expanded into the step), and a
// value parameter beside the index.
#[test]
fn function_children_and_value_parameters() {
    elab(
        "codata Fan(w: Nat) : (n: Nat) -> Type { F(k: (i: Fin(Succ(n))) -> Fan(w, Succ(n))) }
         fn fan(w: Nat, n: Nat) -> Fan(w, n) { F(λ i => fan(w, Succ(n))) }
         fn kid(w: Nat, n: Nat, f: Fan(w, n), i: Fin(Succ(n))) -> Fan(w, Succ(n)) { match f { F(k) => k(i) } }
         theorem fan_kid(w: Nat, n: Nat, i: Fin(Succ(n))): kid(w, n, fan(w, n), i) = fan(w, Succ(n)) { refl }
         fn keep(w: Nat, n: Nat, f: Fan(w, n), b: Nat) -> Fan(w, n) {
             match b { Zero => match f { F(k) => F(k) }, Succ(_) => F(λ i => keep(w, Succ(n), fan(w, Succ(n)), 0)) }
         }
         theorem keep_kid(w: Nat, n: Nat, f: Fan(w, n), i: Fin(Succ(n))): kid(w, n, keep(w, n, f, 0), i) = kid(w, n, f, i) { refl }",
    );
}

// A two-binder telescope whose second type depends on the first, with the
// child's index tuple checked component by component.
#[test]
fn dependent_telescope() {
    elab(
        "codata Dep : (n: Nat) -> (h: n = n) -> Type { D(at: Nat, next: Dep(Succ(n), refl)) }
         fn dep(n: Nat) -> Dep(n, refl) { D(n, dep(Succ(n))) }
         fn at(n: Nat, h: n = n, d: Dep(n, h)) -> Nat { match d { D(a, _) => a } }
         fn nxt(n: Nat, h: n = n, d: Dep(n, h)) -> Dep(Succ(n), refl) { match d { D(_, k) => k } }
         theorem dep_two(n: Nat): at(Succ(n), refl, nxt(n, refl, dep(n))) = Succ(n) { refl }",
    );
}

// -- negative controls -------------------------------------------------------

// The coinduction hypothesis is used only at the index it was stated at.
#[test]
fn self_call_at_the_wrong_index_is_refused() {
    let msg = elab_err(&format!("{STREAM}\nfn bad(s: Stream) -> SBisim(s, s) {{ Same(refl, bad(s)) }}"));
    assert!(msg.contains("result index must be the child's"), "{msg}");
}

// §1: no result annotations on codata, with the reason.
#[test]
fn result_annotations_are_refused() {
    let msg = elab_err("codata Tg : (n: Nat) -> Type { TZ : Tg(0) }");
    assert!(msg.contains("read by observation") && msg.contains("docs/codata-indexed-design.md §1"), "{msg}");
}

#[test]
fn a_use_needs_its_index() {
    let msg = elab_err(&format!("{STREAM}\nfn f(b: SBisim) -> Nat {{ 0 }}"));
    assert!(msg.contains("needs its index"), "{msg}");
    let msg = elab_err(&format!("{STREAM}\nfn f(s: Stream, b: SBisim(s)) -> Nat {{ 0 }}"));
    assert!(msg.contains("index argument(s)"), "{msg}");
}

// Nested constructors above a self-call are generated for unindexed codata
// only (codata-elaborator-design §5.4); an indexed one names its issue.
#[test]
fn nested_guard_is_refused_with_its_issue() {
    let msg = elab_err(&format!("{STREAM}\nfn bad(s: Stream) -> SBisim(s, s) {{ Same(refl, Same(refl, bad(tl(tl(s))))) }}"));
    assert!(msg.contains("issues/codata-nested-guards-indexed.md"), "{msg}");
}

// The β rule is not a guess: a wrong observation is refused by the kernel.
#[test]
fn wrong_observation_is_refused() {
    let msg = elab_err(
        "codata Count : (n: Nat) -> Type { Tick(at: Nat, ok: at = n, next: Count(Succ(n))) }
         fn here(n: Nat, c: Count(n)) -> Nat { match c { Tick(a, _, _) => a } }
         fn later(n: Nat, c: Count(n)) -> Count(Succ(n)) { match c { Tick(_, _, k) => k } }
         fn count(n: Nat) -> Count(n) { Tick(n, refl, count(Succ(n))) }
         theorem wrong(): here(3, later(2, count(2))) = 2 { refl }",
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// A child must be the declaration at its parameters, then one index per
// binder.
#[test]
fn a_child_at_the_wrong_arity_is_refused() {
    let msg = elab_err("codata C : (n: Nat) -> (m: Nat) -> Type { K(next: C(n)) }");
    assert!(msg.contains("one index per binder"), "{msg}");
}

// Images: the index telescope and each child's written index are part of the
// declaration's interface, so an importing module can construct, observe
// and corecurse into it.
#[test]
fn indexed_codata_round_trips_through_images() {
    let dir = std::env::temp_dir().join(format!("heather-codata-indexed-images-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let modules = &[("bisim", STREAM)];
    let cold = support::semantic_test_base_at(modules, dir.clone());
    let expected = cold.psi().clone();
    let mut warm = support::semantic_test_base_at(modules, dir.clone());
    assert_eq!(warm.psi(), &expected);
    let consumer = "import bisim;
         fn sb_sym(s: Stream, t: Stream, b: SBisim(s, t)) -> SBisim(t, s) {
             match b { Same(h, k) => Same(sym(h), sb_sym(tl(s), tl(t), k)) }
         }
         theorem refl_tails(s: Stream): tails(s, s, sb_refl(s)) = sb_refl(tl(s)) { refl }";
    warm.elab_module_source("consumer", consumer)
        .unwrap_or_else(|err| panic!("{}", err.render(consumer)));
    let _ = std::fs::remove_dir_all(dir);
}

// A goal over indexed codata names the declaration and shows its index.
#[test]
fn goals_spell_indexed_codata_by_name() {
    let msg = elab_err(&format!("{STREAM}\ntheorem g(s: Stream, b: SBisim(s, tl(s))): hd(s) = hd(s) {{ ?g }}"));
    assert!(msg.contains("b : SBisim(s, tl(s))"), "{msg}");
}
