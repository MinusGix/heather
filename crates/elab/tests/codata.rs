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

// An existing function child passed whole, not as a λ, in a corecursive
// step: the child is its η-expansion into the step's sum, so its
// observations are the original's, at a neutral tree and a literal one.
#[test]
fn existing_function_child_in_a_corecursive_step() {
    elab(
        "inductive Phase { Waiting, Ticking }
         codata Rose { RNode(label: Nat, kids: Nat -> Rose) }
         fn grow(n: Nat) -> Rose { RNode(n, λ i => grow(Succ(n))) }
         fn lab(r: Rose) -> Nat { match r { RNode(l, _) => l } }
         fn kid(r: Rose, i: Nat) -> Rose { match r { RNode(_, k) => k(i) } }
         fn keep(r: Rose, w: Phase) -> Rose {
             match w { Waiting => match r { RNode(l, k) => RNode(l, k) }, Ticking => RNode(0, λ i => keep(r, Waiting)) }
         }
         theorem keep_open(r: Rose, i: Nat): kid(keep(r, Waiting), i) = kid(r, i) { refl }
         theorem keep_lit(): lab(kid(keep(grow(1), Waiting), 5)) = 2 { refl }
         theorem keep_tick(r: Rose, i: Nat): kid(keep(r, Ticking), i) = keep(r, Waiting) { refl }",
    );
}

// §5.4 — constructors nested above a self-call: the carrier grows one
// pending-node layer per extra constructor, and each layer's observation
// computes by β under `out`, back to the definition itself after the last
// (`tl(tl(pairs(n))) = pairs(…)` by `refl`). Literal and neutral seeds; two
// and three layers; a nested node under a function child whose answer it
// captures, and a `match` there with an existing tree in one arm (the
// `echo` that `function_children_and_dependent_domains` writes with a phase
// seed); an existing function child one layer down, and an answer captured
// by the pending node as the next seed; and an open element type.
#[test]
fn nested_constructors_above_a_self_call() {
    elab(&format!(
        "{STREAM}
         fn pairs(n: Nat) -> Stream {{ SCons(n, SCons(Succ(n), pairs(Succ(Succ(n))))) }}
         fn triples(n: Nat) -> Stream {{ SCons(n, SCons(n, SCons(Succ(n), triples(Succ(n))))) }}
         theorem pairs_lit(): nth(pairs(0), 5) = 5 {{ refl }}
         theorem pairs_open(n: Nat): hd(tl(pairs(n))) = Succ(n) {{ refl }}
         theorem pairs_back(n: Nat): tl(tl(pairs(n))) = pairs(Succ(Succ(n))) {{ refl }}
         theorem triples_lit(): nth(triples(4), 4) = 5 {{ refl }}
         theorem triples_back(n: Nat): tl(tl(tl(triples(n)))) = triples(Succ(n)) {{ refl }}
         inductive Cmd {{ Ask, Say(v: Nat) }}
         codata Tree {{ Ret(r: Nat), Tau(t: Tree), Vis(c: Cmd, k: Nat -> Tree) }}
         fn echo(acc: Nat) -> Tree {{
             Vis(Ask, λ n => match n {{ Zero => Ret(acc), Succ(_) => Tau(echo(add(n, acc))) }})
         }}
         fn answer(t: Tree, n: Nat) -> Tree {{ match t {{ Vis(_, k) => k(n), _ => t }} }}
         fn tau_next(t: Tree) -> Tree {{ match t {{ Tau(u) => u, _ => t }} }}
         fn ret_of(t: Tree) -> Nat {{ match t {{ Ret(r) => r, _ => 0 }} }}
         theorem echo_lit(): tau_next(answer(echo(1), 2)) = echo(3) {{ refl }}
         theorem echo_open(a: Nat, m: Nat): tau_next(answer(echo(a), Succ(m))) = echo(add(Succ(m), a)) {{ refl }}
         theorem echo_stops(a: Nat): ret_of(answer(echo(a), 0)) = a {{ refl }}
         fn chats(v: Nat) -> Tree {{ Vis(Say(v), λ f => Tau(Vis(Say(f), λ g => chats(add(g, v))))) }}
         theorem chats_back(v: Nat, a: Nat, b: Nat): answer(tau_next(answer(chats(v), a)), b) = chats(add(b, v)) {{ refl }}
         codata Two {{ Node(k: Nat -> Two, t: Two) }}
         fn kid2(x: Two, n: Nat) -> Two {{ match x {{ Node(k, _) => k(n) }} }}
         fn next2(x: Two) -> Two {{ match x {{ Node(_, t) => t }} }}
         fn walk(k: Nat -> Two) -> Two {{ Node(k, Node(k, walk(k))) }}
         theorem walk_k(k: Nat -> Two, n: Nat): kid2(next2(walk(k)), n) = k(n) {{ refl }}
         theorem walk_back(k: Nat -> Two): next2(next2(walk(k))) = walk(k) {{ refl }}
         codata Seq<A> {{ Cons(h: A, t: Seq<A>) }}
         fn shd<A>(s: Seq<A>) -> A {{ match s {{ Cons(h, _) => h }} }}
         fn stl<A>(s: Seq<A>) -> Seq<A> {{ match s {{ Cons(_, t) => t }} }}
         fn alt<A>(a: A, b: A) -> Seq<A> {{ Cons(a, Cons(b, alt(a, b))) }}
         theorem alt_open<A>(a: A, b: A): shd(stl(stl(stl(alt(a, b))))) = b {{ refl }}
         theorem alt_back<A>(a: A, b: A): stl(stl(alt(a, b))) = alt(a, b) {{ refl }}"
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
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
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

// A call inside a tree that is not one of the declaration's constructors
// is corecursion *up to* that function, which only a friend takes (§5.5):
// `tl` reads two layers of its argument's tree (the call's constructor and
// its child), so it is not one, even where nested constructors above it
// would be accepted.
#[test]
fn self_call_inside_an_existing_tree_is_refused() {
    let msg = elab_err(&format!("{STREAM}\nfn bad(n: Nat) -> Stream {{ SCons(n, tl(SCons(n, bad(n)))) }}"));
    assert!(msg.contains("nests constructors above a corecursive call"), "{msg}");
    let msg = elab_err(&format!("{STREAM}\nfn bad(n: Nat) -> Stream {{ SCons(n, tl(bad(n))) }}"));
    assert!(msg.contains("`tl` is not a friend of the corecursive `bad`"), "{msg}");
    let msg = elab_err(&format!("{STREAM}\nfn bad(n: Nat) -> Stream {{ SCons(n, SCons(hd(bad(n)), bad(n))) }}"));
    assert!(msg.contains("is not guarded"), "{msg}");
}

// §5.5 — corecursion up to friends. `sadd` reads one layer of each argument
// and calls itself on their children; `smul` (the Hurwitz product of
// formal power series, `(fg)' = f'g + fg'`) corecurses under it, and
// `scale` takes a data argument beside its stream.
const FRIENDS: &str = r#"
fn mul(a: Nat, b: Nat) -> Nat { match a { Zero => 0, Succ(k) => add(b, mul(k, b)) } }
fn sadd(s: Stream, t: Stream) -> Stream {
    match s { SCons(a, s2) => match t { SCons(b, t2) => SCons(add(a, b), sadd(s2, t2)) } }
}
fn smul(f: Stream, g: Stream) -> Stream {
    SCons(mul(hd(f), hd(g)), sadd(smul(tl(f), g), smul(f, tl(g))))
}
fn scale(c: Nat, s: Stream) -> Stream { match s { SCons(a, s2) => SCons(mul(c, a), scale(c, s2)) } }
fn geo(n: Nat) -> Stream { SCons(1, scale(n, geo(n))) }
"#;

// Observations of a corecursion up to a friend compute by `refl` as far as
// the friend's own unfolding does: at neutral streams, at literal ones (the
// Hurwitz square of 1, 2, 3, … is 1, 4, 14, …), and with a fixed parameter
// stored as the friend's data argument.
#[test]
fn corecursion_up_to_a_friend() {
    elab(&format!(
        "{STREAM}{FRIENDS}
         theorem smul_hd(f: Stream, g: Stream): hd(smul(f, g)) = mul(hd(f), hd(g)) {{ refl }}
         theorem smul_tl(f: Stream, g: Stream):
             hd(tl(smul(f, g))) = add(mul(hd(tl(f)), hd(g)), mul(hd(f), hd(tl(g)))) {{ refl }}
         theorem smul_1(): nth(smul(from(1), from(1)), 1) = 4 {{ refl }}
         theorem smul_2(): nth(smul(from(1), from(1)), 2) = 14 {{ refl }}
         theorem geo_3(): nth(geo(2), 3) = 8 {{ refl }}
         theorem geo_open(n: Nat): hd(tl(geo(n))) = mul(n, 1) {{ refl }}"
    ));
}

// A friend whose output is an argument's own first node (`append` at the
// end of its first list), on a codata type with a childless constructor,
// with an existing tree and a corecursive call as its arguments.
#[test]
fn friend_returning_an_argument() {
    elab(&format!(
        "{STREAM}
         codata CoList {{ CNil, CCons(h: Nat, t: CoList) }}
         fn upto(n: Nat) -> CoList {{ match n {{ Zero => CNil, Succ(k) => CCons(n, upto(k)) }} }}
         fn cnth(c: CoList, n: Nat) -> Nat {{
             match n {{
                 Zero => match c {{ CNil => 99, CCons(h, _) => h }},
                 Succ(k) => match c {{ CNil => 99, CCons(_, t) => cnth(t, k) }}
             }}
         }}
         fn app(a: CoList, b: CoList) -> CoList {{
             match a {{ CNil => b, CCons(h, t) => CCons(h, app(t, b)) }}
         }}
         fn cyc(n: Nat) -> CoList {{ CCons(n, app(upto(n), cyc(n))) }}
         theorem cyc_2(): cnth(cyc(2), 2) = 1 {{ refl }}
         theorem cyc_3(): cnth(cyc(2), 3) = 2 {{ refl }}
         theorem cyc_0(): cnth(cyc(0), 5) = 0 {{ refl }}
         theorem cyc_open(n: Nat): cnth(cyc(Succ(n)), 1) = Succ(n) {{ refl }}"
    ));
}

// A friend over function children: its codata argument's child is applied
// under a λ and passed to itself; the definition corecurses under it in a
// `match` arm inside a λ child, beside an existing tree in the other arm.
// Observations read the friend returning its second argument.
#[test]
fn friend_over_function_children() {
    elab(&format!(
        "{STREAM}
         codata Tr {{ Leaf(n: Nat), Node(k: Nat -> Tr) }}
         fn graft(t: Tr, u: Tr) -> Tr {{
             match t {{ Leaf(_) => u, Node(k) => Node(λ x => graft(k(x), u)) }}
         }}
         fn sprout(n: Nat) -> Tr {{
             Node(λ m => match m {{ Zero => Leaf(n), Succ(j) => graft(Leaf(j), sprout(add(n, j))) }})
         }}
         fn at2(t: Tr, x: Nat, y: Nat) -> Nat {{
             match t {{
                 Leaf(n) => n,
                 Node(k) => match k(x) {{
                     Leaf(n) => n,
                     Node(k2) => match k2(y) {{ Leaf(n) => n, Node(_) => 77 }}
                 }}
             }}
         }}
         theorem sprout_0(): at2(sprout(5), 0, 9) = 5 {{ refl }}
         theorem sprout_lit(): at2(sprout(5), 3, 0) = 7 {{ refl }}
         theorem sprout_open(n: Nat): at2(sprout(n), 3, 0) = add(n, 2) {{ refl }}
         theorem sprout_deep(n: Nat): at2(sprout(n), 1, 1) = 77 {{ refl }}"
    ));
}

// A friend declared in another module, replayed from its image: its body is
// re-elaborated over the importer's carrier, under its own module's names.
#[test]
fn friend_from_an_imported_module() {
    let dir = std::env::temp_dir().join(format!("heather-codata-friends-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let streams = format!(
        "{STREAM}
         fn sadd(s: Stream, t: Stream) -> Stream {{
             match s {{ SCons(a, s2) => match t {{ SCons(b, t2) => SCons(add(a, b), sadd(s2, t2)) }} }}
         }}"
    );
    let modules = &[("streams", streams.as_str())];
    let _cold = support::semantic_test_base_at(modules, dir.clone());
    let mut warm = support::semantic_test_base_at(modules, dir.clone());
    let consumer = "import streams;
         fn add(s: Stream, n: Nat) -> Stream { s }
         fn tri(n: Nat) -> Stream { SCons(n, sadd(tri(Succ(n)), from(n))) }
         theorem tri_1(): nth(tri(1), 1) = 3 { refl }
         theorem tri_open(n: Nat): hd(tl(tri(n))) = streams::add(Succ(n), n) { refl }";
    warm.elab_module_source("consumer", consumer)
        .unwrap_or_else(|err| panic!("{}", err.render(consumer)));
    let _ = std::fs::remove_dir_all(dir);
}

// The controls: a wrong observation is refused by the kernel; a friend that
// reads two layers (`skip`, which would make `f` unproductive) and one that
// uses its argument as a tree are not friends; a corecursive call in a
// friend's data argument, or nested constructors beside a friend, are
// refused with their reasons.
#[test]
fn corecursion_up_to_controls() {
    let msg = elab_err(&format!(
        "{STREAM}{FRIENDS}\ntheorem wrong(f: Stream, g: Stream): hd(tl(smul(f, g))) = mul(hd(f), hd(g)) {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
    let skip = "fn skip(s: Stream) -> Stream { match s { SCons(a, s2) => SCons(a, skip(tl(s2))) } }";
    let msg = elab_err(&format!("{STREAM}\n{skip}\nfn f(n: Nat) -> Stream {{ SCons(n, skip(f(n))) }}"));
    assert!(msg.contains("`skip` is not a friend of the corecursive `f`"), "{msg}");
    assert!(msg.contains("`s2`"), "{msg}");
    let peek = "fn peek(s: Stream) -> Stream { SCons(hd(s), peek(s)) }";
    let msg = elab_err(&format!("{STREAM}\n{peek}\nfn f(n: Nat) -> Stream {{ SCons(n, peek(f(n))) }}"));
    assert!(msg.contains("`peek` is not a friend of the corecursive `f`"), "{msg}");
    let msg = elab_err(&format!("{STREAM}{FRIENDS}\nfn f(n: Nat) -> Stream {{ SCons(n, scale(hd(f(n)), f(n))) }}"));
    assert!(msg.contains("data argument of the friend `scale`"), "{msg}");
    let msg = elab_err(&format!("{STREAM}{FRIENDS}\nfn f(n: Nat) -> Stream {{ SCons(n, SCons(n, sadd(f(n), f(n)))) }}"));
    assert!(msg.contains("nests constructors above a corecursive call"), "{msg}");
}

// A nested layer's observation is computed, not guessed: a wrong one is
// refused by the kernel, and the tree two layers down is not the seed one
// layer down.
#[test]
fn nested_wrong_observation_is_refused() {
    let pairs = "fn pairs(n: Nat) -> Stream { SCons(n, SCons(Succ(n), pairs(Succ(Succ(n))))) }";
    let msg = elab_err(&format!("{STREAM}\n{pairs}\ntheorem wrong(n: Nat): hd(tl(pairs(n))) = n {{ refl }}"));
    assert!(msg.contains("NotConvertible"), "{msg}");
    let msg = elab_err(&format!("{STREAM}\n{pairs}\ntheorem wrong(n: Nat): tl(pairs(n)) = pairs(Succ(n)) {{ refl }}"));
    assert!(msg.contains("NotConvertible"), "{msg}");
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
