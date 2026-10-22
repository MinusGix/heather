//! Acceptance for `codata` declarations, lowered onto the kernel's `M` /
//! `corec` / `out` (`docs/codata-elaborator-design.md`,
//! `issues/codata-elaborator.md`), against the four axes of
//! `docs/testing-generated-terms.md`: literal *and* neutral seeds and
//! scrutinees, an open element type, checking positions, and a negative
//! control for every rule the lowering enforces.
//!
//! Every declaration is re-checked by the real kernel, so a wrong encoding is
//! a rejection; the `refl` theorems are what catch a *well-typed* wrong one —
//! each is an observation the corecursion's β rule (under `out`) must compute.

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
fn nth(s: Stream, n: Nat) -> Nat { match n { Zero => hd(s), Succ(k) => nth(tl(s), k) } }
fn add(a: Nat, b: Nat) -> Nat { match a { Zero => b, Succ(k) => Succ(add(k, b)) } }
fn zeros() -> Stream { SCons(0, zeros()) }
fn from(n: Nat) -> Stream { SCons(n, from(Succ(n))) }
"#;

// §3 — constructors build trees, `match` observes them, at a literal payload
// and in a checking position (the constructor is an argument).
#[test]
fn constructors_and_observation() {
    elab(&format!(
        "{STREAM}
         theorem ctor_hd(): hd(SCons(3, zeros())) = 3 {{ refl }}
         theorem ctor_open(n: Nat, s: Stream): hd(SCons(n, s)) = n {{ refl }}
         theorem ctor_tl(n: Nat, s: Stream): tl(SCons(n, s)) = s {{ refl }}"
    ));
}

// §5 — one varying parameter: observations compute at a literal seed and at
// a neutral one, and through `nth`, structural recursion on a `Nat` beside
// the stream.
#[test]
fn corecursion_computes_under_observation() {
    elab(&format!(
        "{STREAM}
         theorem zeros_3(): nth(zeros(), 3) = 0 {{ refl }}
         theorem from_lit(): nth(from(2), 3) = 5 {{ refl }}
         theorem from_open(n: Nat): hd(tl(tl(from(n)))) = Succ(Succ(n)) {{ refl }}
         theorem tl_from(n: Nat): tl(from(n)) = from(Succ(n)) {{ refl }}"
    ));
}

// §5.1 — fixed parameters stay outer binders; several varying ones become
// the carrier's Σ-tuple, including two of the same type swapped in the call.
#[test]
fn fixed_and_varying_parameters() {
    elab(&format!(
        "{STREAM}
         fn konst(a: Nat) -> Stream {{ SCons(a, konst(a)) }}
         fn fib(a: Nat, b: Nat) -> Stream {{ SCons(a, fib(b, add(a, b))) }}
         fn interleave(a: Stream, b: Stream) -> Stream {{
             match a {{ SCons(h, t) => SCons(h, interleave(b, t)) }}
         }}
         theorem konst_open(a: Nat): nth(konst(a), 4) = a {{ refl }}
         theorem fib_6(): nth(fib(0, 1), 6) = 8 {{ refl }}
         theorem il_lit(): nth(interleave(from(0), zeros()), 4) = 2 {{ refl }}
         theorem il_open(n: Nat): nth(interleave(from(n), zeros()), 2) = Succ(n) {{ refl }}"
    ));
}

// §5.2 — the step's two positions reached through control flow: a `match`
// in step position (on a stream and on a `Nat`), and an existing tree in
// step position (`zeros()` once the countdown ends).
#[test]
fn step_positions_through_match() {
    elab(&format!(
        "{STREAM}
         fn smap(s: Stream) -> Stream {{ match s {{ SCons(h, t) => SCons(Succ(h), smap(t)) }} }}
         fn countdown(n: Nat) -> Stream {{
             match n {{ Zero => zeros(), Succ(k) => SCons(n, countdown(k)) }}
         }}
         theorem smap_open(n: Nat): nth(smap(from(n)), 2) = Succ(Succ(Succ(n))) {{ refl }}
         theorem cd_end(): nth(countdown(2), 4) = 0 {{ refl }}
         theorem cd_mid(): nth(countdown(3), 1) = 2 {{ refl }}"
    ));
}

// Several constructors, one of them childless: a colist ends.
#[test]
fn colists_end() {
    elab(&format!(
        "{STREAM}
         codata CoList {{ CNil, CCons(h: Nat, t: CoList) }}
         fn upto(n: Nat) -> CoList {{ match n {{ Zero => CNil, Succ(k) => CCons(n, upto(k)) }} }}
         fn len2(c: CoList) -> Nat {{
             match c {{ CNil => 0, CCons(_, t) => match t {{ CNil => 1, CCons(_, _) => 2 }} }}
         }}
         fn of_stream(s: Stream) -> CoList {{ match s {{ SCons(h, t) => CCons(h, of_stream(t)) }} }}
         theorem upto_1(): len2(upto(1)) = 1 {{ refl }}
         theorem upto_5(): len2(upto(5)) = 2 {{ refl }}
         theorem never_ends(s: Stream): len2(of_stream(s)) = 2 {{ refl }}"
    ));
}

// Function children, with a domain that depends on the payload before it —
// the interaction-tree shape, with real divergence.
#[test]
fn function_children_and_dependent_domains() {
    elab(&format!(
        "{STREAM}
         inductive Flag {{ Yes, No }}
         inductive Cmd {{ Ask, Say(v: Nat) }}
         fn Resp(c: Cmd) -> Type {{ match c {{ Ask => Nat, Say(_) => Flag }} }}
         codata Tree {{ Ret(r: Nat), Tau(t: Tree), Vis(c: Cmd, k: Resp(c) -> Tree) }}
         fn spin() -> Tree {{ Tau(spin()) }}
         fn reads(c: Cmd) -> Tree {{ Vis(c, λ r => reads(c)) }}
         inductive Phase {{ Waiting, Ticking }}
         fn echo(w: Phase) -> Tree {{
             match w {{ Waiting => Vis(Ask, λ n => echo(Ticking)), Ticking => Tau(echo(Waiting)) }}
         }}
         fn tau_next(t: Tree) -> Tree {{ match t {{ Tau(u) => u, _ => t }} }}
         fn is_tau(t: Tree) -> Flag {{ match t {{ Tau(_) => Yes, _ => No }} }}
         fn is_vis(t: Tree) -> Flag {{ match t {{ Vis(_, _) => Yes, _ => No }} }}
         theorem spin_spins(): is_tau(tau_next(tau_next(spin()))) = Yes {{ refl }}
         theorem reads_open(c: Cmd): is_vis(reads(c)) = Yes {{ refl }}
         theorem echo_ticks(): is_vis(tau_next(echo(Ticking))) = Yes {{ refl }}
         codata Rose {{ RNode(label: Nat, kids: Nat -> Rose) }}
         fn grow(n: Nat) -> Rose {{ RNode(n, λ i => grow(add(n, i))) }}
         fn lab(r: Rose) -> Nat {{ match r {{ RNode(l, _) => l }} }}
         fn kid(r: Rose, i: Nat) -> Rose {{ match r {{ RNode(_, k) => k(i) }} }}
         theorem grow_kid(): lab(kid(kid(grow(1), 2), 3)) = 6 {{ refl }}
         fn leafy(n: Nat, m: Nat) -> Rose {{ RNode(n, λ i => RNode(m, λ j => grow(add(i, j)))) }}
         theorem leafy_open(n: Nat, m: Nat): lab(kid(leafy(n, m), 0)) = m {{ refl }}
         theorem leafy_deep(n: Nat, m: Nat): lab(kid(kid(leafy(n, m), 2), 3)) = 5 {{ refl }}"
    ));
}

// The open element type: type parameters on the declaration and on a
// corecursive function, with the arguments inferred from a codata argument.
#[test]
fn open_element_types() {
    elab(
        "inductive Flag { Yes, No }
         codata Seq<A> { Cons(h: A, t: Seq<A>) }
         fn shd<A>(s: Seq<A>) -> A { match s { Cons(h, _) => h } }
         fn stl<A>(s: Seq<A>) -> Seq<A> { match s { Cons(_, t) => t } }
         fn rep<A>(a: A) -> Seq<A> { Cons(a, rep(a)) }
         theorem rep_hd<A>(a: A): shd(stl(stl(rep(a)))) = a { refl }
         codata ITree<E, R> { Ret(r: R), Tau(t: ITree<E, R>), Vis(e: E, k: Nat -> ITree<E, R>) }
         fn spin<E, R>() -> ITree<E, R> { Tau(spin()) }
         fn is_tau<E, R>(t: ITree<E, R>) -> Flag { match t { Tau(_) => Yes, _ => No } }
         theorem spin_tau<E, R>(): is_tau(spin<E, R>()) = Yes { refl }",
    );
}

const ITREE_MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("itree", include_str!("../../../lib/std/itree.hthr")),
];

// Value parameters (`docs/inductive-value-parameters.md`): the interaction
// tree over a record of events, diverging for real, and its cut into the
// finite library's `ITree` at a depth — the bridge's data half (design §6).
#[test]
fn value_parameters_and_approximation() {
    let mut e = support::semantic_test_base(ITREE_MODULES);
    let src = "import itree;
         codata CoTree<R>(E: Events) {
             CRet(r: R), CTau(t: CoTree<R>(E)), CVis(c: E.Cmd, k: E.Resp(c) -> CoTree<R>(E))
         }
         fn spin<R>(E: Events) -> CoTree<R>(E) { CTau(spin(E)) }
         fn trigger<R>(E: Events, c: E.Cmd, r: R) -> CoTree<R>(E) { CVis(c, λ a => CRet(r)) }
         fn approx<R>(E: Events, n: Nat, t: CoTree<R>(E)) -> ITree<R>(E) {
             match n {
                 Zero => Cut,
                 Succ(k) => match t {
                     CRet(r) => Ret(r),
                     CTau(u) => Tau(approx(E, k, u)),
                     CVis(c, f) => Vis(c, λ a => approx(E, k, f(a))),
                 },
             }
         }
         theorem spin_cut<R>(E: Events): approx(E, 2, spin<R>(E)) = Tau(Tau(Cut)) { refl }
         theorem trigger_cut<R>(E: Events, c: E.Cmd, r: R):
             approx(E, 2, trigger(E, c, r)) = Vis(c, λ a => Ret(r)) { refl }";
    e.elab_module_source("cotree", src).unwrap_or_else(|err| panic!("{}", err.render(src)));
}

// §6 — every declaration is bound at layer c, codata or not: `M`, `corec`
// and `out` are admitted there, with `TmM` their code
// (docs/kernel-m-codes-design.md).
#[test]
fn codata_declarations_are_code() {
    let e = elab(&format!(
        "{STREAM}
         fn third() -> Nat {{ nth(from(1), 2) }}
         theorem third_is(): third() = 3 {{ refl }}
         fn plain(n: Nat) -> Nat {{ Succ(n) }}"
    ));
    use heather_kernel::layer::Layer;
    for name in ["hd", "zeros", "from", "third", "third_is", "plain", "add"] {
        assert_eq!(e.global_layer(name), Some(Layer::Code), "`{name}`");
    }
}

// §6 — codata has a code, so it is a type argument like any other: written
// (`id<Stream>`), inferred, and inside another type's argument (`Pair`).
#[test]
fn codata_as_a_type_argument() {
    elab(&format!(
        "{STREAM}
         fn id<A>(a: A) -> A {{ a }}
         theorem written(): hd(id<Stream>(from(2))) = 2 {{ refl }}
         theorem inferred(n: Nat): hd(tl(id(from(n)))) = Succ(n) {{ refl }}
         record Two<A> {{ fst: A, snd: A }}
         fn both(n: Nat) -> Two<Stream> {{ Two<Stream>(fst := from(n), snd := zeros()) }}
         theorem both_fst(n: Nat): hd(both(n).fst) = n {{ refl }}"
    ));
}

// Images: a codata declaration and its corecursive functions written to a
// module image and replayed, then used from a module that imports them.
#[test]
fn codata_round_trips_through_images() {
    let dir = std::env::temp_dir().join(format!("heather-codata-images-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let modules = &[("streams", STREAM)];
    let cold = support::semantic_test_base_at(modules, dir.clone());
    let expected = cold.psi().clone();
    let mut warm = support::semantic_test_base_at(modules, dir.clone());
    assert_eq!(warm.psi(), &expected);
    let consumer = "import streams;
         fn evens(n: Nat) -> Stream { SCons(n, evens(Succ(Succ(n)))) }
         theorem evens_2(n: Nat): nth(evens(n), 2) = Succ(Succ(Succ(Succ(n)))) { refl }
         theorem from_imported(): nth(from(4), 1) = 5 { refl }";
    warm.elab_module_source("consumer", consumer)
        .unwrap_or_else(|err| panic!("{}", err.render(consumer)));
    let _ = std::fs::remove_dir_all(dir);
}

// A goal over codata names the declaration, not its `M` encoding.
#[test]
fn goals_spell_codata_by_name() {
    let msg = elab_err(&format!(
        "{STREAM}
         codata Seq<A> {{ Cons(h: A, t: Seq<A>) }}
         theorem g(s: Stream, q: Seq<Nat>): hd(s) = hd(s) {{ ?g }}"
    ));
    assert!(msg.contains("s : Stream") && msg.contains("q : Seq<Nat>"), "{msg}");
}

// -- negative controls -------------------------------------------------------

// The β rule is not a guess: a wrong observation is refused by the kernel.
#[test]
fn wrong_observation_is_refused() {
    let msg = elab_err(&format!("{STREAM}\ntheorem wrong(n: Nat): hd(tl(from(n))) = n {{ refl }}"));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// No η for M: a corecursive tree is not definitionally its one-step
// unfolding written with the constructor (docs/kernel-coinduction-design.md
// §2.1; bisimilarity is the equation, not conversion).
#[test]
fn no_eta_for_codata() {
    let msg = elab_err(&format!(
        "{STREAM}\ntheorem no_eta(n: Nat): from(n) = SCons(n, from(Succ(n))) {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn unguarded_self_call_is_refused() {
    let msg = elab_err(&format!("{STREAM}\nfn bad() -> Stream {{ bad() }}"));
    assert!(msg.contains("is not guarded"), "{msg}");
}

// A self-call under an observation is not a child of the step's
// constructor, even though it sits inside one syntactically.
#[test]
fn self_call_under_an_observation_is_refused() {
    let msg = elab_err(&format!("{STREAM}\nfn bad(n: Nat) -> Stream {{ SCons(hd(bad(n)), bad(n)) }}"));
    assert!(msg.contains("is not guarded"), "{msg}");
    let msg = elab_err(&format!("{STREAM}\nfn bad(n: Nat) -> Stream {{ tl(bad(n)) }}"));
    assert!(msg.contains("is not guarded"), "{msg}");
}

#[test]
fn nested_guard_is_refused_with_its_issue() {
    let msg = elab_err(&format!(
        "{STREAM}\nfn bad(n: Nat) -> Stream {{ SCons(n, SCons(n, bad(n))) }}"
    ));
    assert!(msg.contains("issues/codata-nested-guards.md"), "{msg}");
}

#[test]
fn recursion_out_of_codata_is_refused() {
    let msg = elab_err(&format!(
        "{STREAM}\nfn count(s: Stream) -> Nat {{ match s {{ SCons(_, t) => Succ(count(t)) }} }}"
    ));
    assert!(msg.contains("codata has no structural order"), "{msg}");
}

// Indexed codata reads its index by observation: a result annotation is
// refused (docs/codata-indexed-design.md §1; the acceptance is
// `codata_indexed.rs`).
#[test]
fn indexed_codata_refuses_result_annotations() {
    let msg = elab_err("codata Tg : (n: Nat) -> Type { TZ : Tg(0) }");
    assert!(msg.contains("docs/codata-indexed-design.md §1"), "{msg}");
}
