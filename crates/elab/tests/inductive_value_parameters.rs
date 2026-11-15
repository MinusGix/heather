//! Value parameters on `inductive` (docs/language/surface-value-parameters.md §6):
//! `inductive Res(m: Nat) { Good(n: Nat, h: dbl(n) = m), Bad(why: Nat), Gone }`,
//! at tier 0, tier 1 (`Tree(m)`, lowered onto `Wf`) and tier 2
//! (`ITree<R>(E)`, lowered onto `W`; issues/tier2-value-parameters.md).
//!
//! The lowering is the record's: every constructor's field types are lowered
//! with the parameters bound as aliases at the use site's depth
//! (`lower_ctor`), so a parameter is *substituted*, never fibred over. What an
//! `inductive` adds is the classifier: a recursive occurrence is a child only
//! when it is `D<p̄>(v̄)` with the declaration's own parameters, in order — any
//! other value argument would be an index, and lowering it as a child would
//! drop the difference silently. §6 below is that refusal.
//!
//! **Why most of this file is propositional** (§2 of the design doc). An
//! un-shifted parameter is captured by a field binder and writes a different,
//! usually trivially inhabited, proposition — and the kernel accepts both.
//! Each constructor puts the parameter under a different number of binders
//! (the tag, then every earlier *payload* field; at tier 1 the children are
//! absent from the shape, so a payload after a child is the exposed case), so
//! every constructor that mentions the parameter has its own observer: a
//! canonical inhabitant of the captured spelling must be refused at an open
//! parameter, and an arm's field must have the substituted type when it is
//! used at that parameter (`Witness(m)`).
//!
//! The four axes of docs/testing-generated-terms.md: literal scrutinees
//! (closed computation by `refl`) and neutral ones (every `match` below is at
//! an open `m`); an open element type (`Bag<A>(m)`, `ITree<R>(E)`); checking
//! positions (a declared result, an argument, an annotated `let`); and
//! negative controls at both levels — the declaration (§6) and the
//! proposition (§2, §4, §5).

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated:\n{src}"),
        Err(err) => err.render(src),
    }
}

/// `dbl` is a recursive `fn`, so `dbl(n) = m` at a neutral `n` is a stuck
/// eliminator inside a field type, and at a neutral `m` nothing closes it.
/// `Two` puts the parameter at two depths; `Witness` is the record that reads
/// an arm's evidence back out at the parameter it was built at.
const BASE: &str = r#"
fn dbl(n: Nat) -> Nat {
    match n { Zero => 0, Succ(k) => Succ(Succ(dbl(k))) }
}
record Witness(m: Nat) { n: Nat, h: dbl(n) = m }
inductive Two(m: Nat) { A(n: Nat, h: dbl(n) = m), B(x: Nat, y: Nat, h: dbl(y) = m), C }
"#;

// -- 1: tier 0 forms, builds and matches -----------------------------------

/// Every constructor builds in every checking position — a declared result,
/// an argument, an annotated `let` — at a literal parameter and at an open
/// one; a nullary constructor builds at any parameter.
#[test]
fn a_value_parameterized_inductive_builds_in_checking_positions() {
    ok(&format!(
        r#"
        {BASE}
        fn a4() -> Two(4) {{ A(2, refl) }}
        fn b4() -> Two(4) {{ B(9, 2, refl) }}
        fn c_any(m: Nat) -> Two(m) {{ C }}
        theorem a_open(n: Nat): Two(dbl(n)) {{ A(n, refl) }}
        theorem b_open(n: Nat): Two(dbl(n)) {{ B(7, n, refl) }}
        theorem from_hyp(m: Nat, y: Nat, h: dbl(y) = m): Two(m) {{ B(0, y, h) }}
        fn takes(m: Nat, t: Two(m)) -> Nat {{ 0 }}
        fn as_argument() -> Nat {{ takes(4, B(1, 2, refl)) }}
        fn as_let(m: Nat) -> Nat {{ let t: Two(m) = C; takes(m, t) }}
        "#
    ));
}

/// A `match` at an open parameter hands each arm its fields at the
/// *substituted* types: `h` is `dbl(n) = m` in `A` and `dbl(y) = m` in `B`,
/// which is exactly what `Witness(m)` asks for. Then the same function at a
/// literal scrutinee computes.
#[test]
fn a_match_reads_each_constructor_at_the_parameter() {
    ok(&format!(
        r#"
        {BASE}
        fn wit(m: Nat, t: Two(m), w: Witness(m)) -> Witness(m) {{
            match t {{ A(n, h) => Witness(n, h), B(_, y, h) => Witness(y, h), C => w }}
        }}
        theorem wit_a(): wit(4, A(2, refl), Witness(2, refl)).n = 2 {{ refl }}
        theorem wit_b(): wit(6, B(9, 3, refl), Witness(3, refl)).n = 3 {{ refl }}
        theorem wit_open(m: Nat, w: Witness(m)): wit(m, C, w) = w {{ refl }}
        "#
    ));
}

// -- 2: the propositional observers, one per constructor --------------------

/// **The load-bearing test.** Under a captured parameter each of these is
/// the canonical inhabitant of the wrong spelling (`dbl 0 = 0`, or
/// `dbl m = m` when the capture lands on the witness); under the right one
/// they are all false at an open `m`. `B`'s parameter sits two binders deeper
/// than `A`'s, so the two constructors are separate observers.
#[test]
fn an_unshifted_parameter_would_be_provable_and_is_not() {
    for body in ["A(0, refl)", "A(m, refl)", "B(0, 0, refl)", "B(m, m, refl)"] {
        let m = bad(&format!("{BASE}\ntheorem t(m: Nat): Two(m) {{ {body} }}"));
        assert!(m.contains("NotConvertible"), "{body}: {m}");
    }
}

/// Two parameters are two types: a value at one does not inhabit another,
/// and the display says which parameter they differ in.
#[test]
fn a_value_at_one_parameter_is_not_at_another() {
    let m = bad(&format!("{BASE}\nfn wrong() -> Two(5) {{ A(2, refl) }}"));
    assert!(m.contains("NotConvertible"), "{m}");
    let m = bad(&format!("{BASE}\nfn coerce(t: Two(4)) -> Two(5) {{ t }}"));
    assert!(m.contains("this has type `Two(4)`, but `Two(5)` is expected here"), "{m}");
}

/// Inference position has nothing that fixes the parameter, at a nullary
/// constructor as at any other, and says where it would be fixed.
#[test]
fn inference_position_names_the_checking_positions() {
    let m = bad(&format!("{BASE}\nfn f() -> Nat {{ let x = C; 0 }}"));
    assert!(m.contains("cannot infer the value argument `m` of `Two`"), "{m}");
}

// -- 3-4: tier 1 -----------------------------------------------------------

/// `Node`'s payload comes *after* a child: the children are not in the
/// `Wf`'s shape, so `k` and `hk` sit under fewer binders than their written
/// position says. That is the shift a wrong count would get wrong.
const TREE: &str = r#"
inductive Tree(m: Nat) {
    Leaf(n: Nat, h: dbl(n) = m),
    Node(l: Tree(m), k: Nat, hk: dbl(k) = m, r: Tree(m)),
}
fn leaf(m: Nat, n: Nat, h: dbl(n) = m) -> Tree(m) { Leaf(n, h) }
fn node(m: Nat, l: Tree(m), k: Nat, hk: dbl(k) = m, r: Tree(m)) -> Tree(m) { Node(l, k, hk, r) }
fn leftmost(m: Nat, t: Tree(m)) -> Witness(m) {
    match t { Leaf(n, h) => Witness(n, h), Node(l, _, _, _) => leftmost(m, l) }
}
fn mid(m: Nat, t: Tree(m), w: Witness(m)) -> Witness(m) {
    match t { Leaf(_, _) => w, Node(_, k, hk, _) => Witness(k, hk) }
}
fn mirror(m: Nat, t: Tree(m)) -> Tree(m) {
    match t { Leaf(n, h) => Leaf(n, h), Node(l, k, hk, r) => Node(mirror(m, r), k, hk, mirror(m, l)) }
}
fn t4() -> Tree(4) { Node(Leaf(2, refl), 2, refl, Node(Leaf(2, refl), 2, refl, Leaf(2, refl))) }
"#;

/// The recursive declaration: builds nested at a literal parameter,
/// recurses at an open one, computes by `refl` at a literal scrutinee and
/// unfolds by `refl` at an open constructor form.
#[test]
fn a_recursive_value_parameterized_inductive_builds_and_recurses() {
    ok(&format!(
        r#"
        {BASE}{TREE}
        theorem lm(): leftmost(4, t4()).n = 2 {{ refl }}
        theorem lm_mirror(): leftmost(4, mirror(4, t4())).n = 2 {{ refl }}
        theorem mid_open(m: Nat, l: Tree(m), k: Nat, hk: dbl(k) = m, r: Tree(m), w: Witness(m)):
            mid(m, Node(l, k, hk, r), w) = Witness(k, hk) {{ refl }}
        theorem mirror_open(m: Nat, l: Tree(m), k: Nat, hk: dbl(k) = m, r: Tree(m)):
            mirror(m, Node(l, k, hk, r)) = Node(mirror(m, r), k, hk, mirror(m, l)) {{ refl }}
        theorem lm_ind(m: Nat, t: Tree(m)): leftmost(m, mirror(m, mirror(m, t))) = leftmost(m, t) {{
            match t {{ Leaf(n, h) => refl, Node(l, _, _, _) => lm_ind(m, l) }}
        }}
        "#
    ));
}

/// The tier-1 observers: a leaf's and a node's evidence, at an open
/// parameter, by the captured spelling's canonical inhabitant.
#[test]
fn tier_1_unshifted_parameters_are_not_provable() {
    let m = bad(&format!("{BASE}{TREE}\ntheorem t(m: Nat): Tree(m) {{ Leaf(0, refl) }}"));
    assert!(m.contains("NotConvertible"), "{m}");
    let m = bad(&format!(
        "{BASE}{TREE}\ntheorem t(m: Nat, l: Tree(m), r: Tree(m)): Tree(m) {{ Node(l, 0, refl, r) }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
    let m = bad(&format!(
        "{BASE}{TREE}\ntheorem t(m: Nat, l: Tree(m), r: Tree(m)): Tree(m) {{ Node(l, m, refl, r) }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

/// No-confusion at an open parameter, both halves, including injectivity at
/// a child and at a payload after a child.
#[test]
fn no_confusion_at_an_open_parameter() {
    ok(&format!(
        r#"
        {BASE}{TREE}
        theorem leaf_ne(m: Nat, n: Nat, h: dbl(n) = m, l: Tree(m), k: Nat, hk: dbl(k) = m,
                        r: Tree(m), p: leaf(m, n, h) = node(m, l, k, hk, r)): n = 0 {{ absurd(p) }}
        theorem node_inj_l(m: Nat, l: Tree(m), k: Nat, hk: dbl(k) = m, r: Tree(m),
                           l2: Tree(m), k2: Nat, hk2: dbl(k2) = m, r2: Tree(m),
                           p: node(m, l, k, hk, r) = node(m, l2, k2, hk2, r2)): l = l2 {{ inj(p) }}
        theorem node_inj_k(m: Nat, l: Tree(m), k: Nat, hk: dbl(k) = m, r: Tree(m),
                           l2: Tree(m), k2: Nat, hk2: dbl(k2) = m, r2: Tree(m),
                           p: node(m, l, k, hk, r) = node(m, l2, k2, hk2, r2)): k = k2 {{ inj(p, 1) }}
        "#
    ));
}

/// Type parameters and value parameters compose on a recursive declaration:
/// the open element type `A` beside the parameter.
#[test]
fn an_open_element_type_beside_a_value_parameter() {
    ok(&format!(
        r#"
        {BASE}
        inductive Bag<A>(m: Nat) {{ Nil0, Put(a: A, n: Nat, h: dbl(n) = m, rest: Bag<A>(m)) }}
        fn count<A>(m: Nat, b: Bag<A>(m)) -> Nat {{
            match b {{ Nil0 => 0, Put(_, _, _, rest) => Succ(count(m, rest)) }}
        }}
        fn first<A>(m: Nat, b: Bag<A>(m), d: A) -> A {{ match b {{ Nil0 => d, Put(a, _, _, _) => a }} }}
        fn evidence<A>(m: Nat, b: Bag<A>(m), w: Witness(m)) -> Witness(m) {{
            match b {{ Nil0 => w, Put(_, n, h, _) => Witness(n, h) }}
        }}
        fn b2() -> Bag<Nat>(4) {{ Put(1, 2, refl, Put(3, 2, refl, Nil0)) }}
        theorem cnt(): count(4, b2()) = 2 {{ refl }}
        theorem fst(): first(4, b2(), 0) = 1 {{ refl }}
        theorem fst_open<A>(m: Nat, a: A, n: Nat, h: dbl(n) = m, rest: Bag<A>(m), d: A):
            first(m, Put(a, n, h, rest), d) = a {{ refl }}
        "#
    ));
    let m = bad(&format!(
        r#"
        {BASE}
        inductive Bag<A>(m: Nat) {{ Nil0, Put(a: A, n: Nat, h: dbl(n) = m, rest: Bag<A>(m)) }}
        theorem t<A>(m: Nat, a: A): Bag<A>(m) {{ Put(a, 0, refl, Nil0) }}
        "#
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

// -- 5: tier 2 -------------------------------------------------------------

/// The issue's own declaration (issues/tier2-value-parameters.md): the events
/// are a *value*, and `Vis`'s function child has a domain read off it.
const ITREE: &str = r#"
record Events { Cmd: Type, Resp: Cmd -> Type }
inductive ITree<R>(E: Events) {
    Ret(r: R),
    Tau(t: ITree<R>(E)),
    Vis(c: E.Cmd, k: E.Resp(c) -> ITree<R>(E)),
}
inductive Q { Ask, Tell(v: Nat) }
inductive Ack { Done }
fn QR(q: Q) -> Type { match q { Ask => Nat, Tell(v) => Ack } }
fn ev() -> Events { Events(Q, QR) }
fn reply(q: Q) -> QR(q) { match q { Ask => 7, Tell(v) => Done } }
fn first(t: ITree<Nat>(ev())) -> Nat {
    match t { Ret(r) => r, Tau(s) => first(s), Vis(c, k) => first(k(reply(c))) }
}
fn depth<R>(E: Events, a: (c: E.Cmd) -> E.Resp(c), t: ITree<R>(E)) -> Nat {
    match t { Ret(_) => 0, Tau(s) => Succ(depth(E, a, s)), Vis(c, k) => Succ(depth(E, a, k(a(c)))) }
}
fn leaf_of<R>(E: Events, a: (c: E.Cmd) -> E.Resp(c), t: ITree<R>(E)) -> R {
    match t { Ret(r) => r, Tau(s) => leaf_of(E, a, s), Vis(c, k) => leaf_of(E, a, k(a(c))) }
}
fn rebuild<R>(E: Events, t: ITree<R>(E)) -> ITree<R>(E) {
    match t { Ret(r) => Ret(r), Tau(s) => Tau(rebuild(E, s)), Vis(c, k) => Vis(c, λ x => rebuild(E, k(x))) }
}
"#;

/// Declares; every constructor builds at an open `E` and an open `R`; a
/// `match` recurses through `k` at an open `E`; closed computation through
/// `k` by `refl`; β at open children; induction through every kind.
#[test]
fn itree_with_value_events_declares_builds_and_recurses() {
    ok(&format!(
        r#"
        {ITREE}
        fn ret<R>(E: Events, r: R) -> ITree<R>(E) {{ Ret(r) }}
        fn tau<R>(E: Events, t: ITree<R>(E)) -> ITree<R>(E) {{ Tau(t) }}
        fn vis<R>(E: Events, c: E.Cmd, k: E.Resp(c) -> ITree<R>(E)) -> ITree<R>(E) {{ Vis(c, k) }}
        fn echo() -> ITree<Nat>(ev()) {{ Vis(Ask, λ n => Tau(Ret(n))) }}
        theorem f_echo(): first(echo()) = 7 {{ refl }}
        theorem f_tell(): first(Vis(Tell(1), λ d => Ret(3))) = 3 {{ refl }}
        theorem d_echo(): depth(ev(), reply, echo()) = 2 {{ refl }}
        theorem o_vis<R>(E: Events, a: (c: E.Cmd) -> E.Resp(c), c: E.Cmd, k: E.Resp(c) -> ITree<R>(E)):
            depth<R>(E, a, Vis(c, k)) = Succ(depth(E, a, k(a(c)))) {{ refl }}
        theorem l_rebuild<R>(E: Events, a: (c: E.Cmd) -> E.Resp(c), t: ITree<R>(E)):
            leaf_of(E, a, rebuild(E, t)) = leaf_of(E, a, t) {{
            match t {{
                Ret(r) => refl,
                Tau(s) => l_rebuild(E, a, s),
                Vis(c, k) => l_rebuild(E, a, k(a(c))),
            }}
        }}
        "#
    ));
}

/// The tier-2 observers: payload evidence beside a function child, and a
/// function child whose *domain* is read off the parameter.
#[test]
fn tier_2_parameters_reach_payloads_and_domains() {
    ok(&format!(
        r#"
        {BASE}
        inductive Br(m: Nat) {{ Stop, Go(n: Nat, h: dbl(n) = m, k: Nat -> Br(m)) }}
        fn evidence(m: Nat, b: Br(m), w: Witness(m)) -> Witness(m) {{
            match b {{ Stop => w, Go(n, h, _) => Witness(n, h) }}
        }}
        fn deep(m: Nat, b: Br(m)) -> Nat {{ match b {{ Stop => 0, Go(_, _, k) => Succ(deep(m, k(0))) }} }}
        theorem deep2(): deep(4, Go(2, refl, λ x => Go(2, refl, λ y => Stop))) = 2 {{ refl }}
        inductive Ch(m: Nat) {{ End, Pick(k: Fin(m) -> Ch(m)) }}
        fn pick(m: Nat, k: Fin(m) -> Ch(m)) -> Ch(m) {{ Pick(k) }}
        "#
    ));
    let m = bad(&format!(
        r#"
        {BASE}
        inductive Br(m: Nat) {{ Stop, Go(n: Nat, h: dbl(n) = m, k: Nat -> Br(m)) }}
        theorem t(m: Nat): Br(m) {{ Go(0, refl, λ x => Stop) }}
        "#
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

// -- 6: declaration-level refusals -----------------------------------------

/// Anything but the uniform occurrence is refused by name, at both recursive
/// tiers: a varying argument, a permuted list, a bare `D`, another value
/// parameter's events. Each of these would be an index lowered as a child.
#[test]
fn a_non_uniform_occurrence_is_refused_by_name() {
    let uniform = "a recursive occurrence must be";
    for (src, own) in [
        ("inductive D(m: Nat) { E, F(x: D(Succ(m))) }", "`D(m)`"),
        ("inductive D(m: Nat, k: Nat) { E, F(x: D(k, m)) }", "`D(m, k)`"),
        ("inductive D(m: Nat) { E, F(x: D) }", "`D(m)`"),
        ("inductive D(m: Nat) { E, F(x: Nat -> D(Succ(m))) }", "`D(m)`"),
    ] {
        let m = bad(src);
        assert!(m.contains(uniform) && m.contains(own), "{src}: {m}");
    }
    let m = bad(&format!(
        "{ITREE}\ninductive T2<R>(E: Events, F: Events) {{ Ret2(r: R), Tau2(t: T2<R>(F, E)) }}"
    ));
    assert!(m.contains("`T2<R>(E, F)`"), "{m}");
    let m = bad(&format!(
        "{ITREE}\ninductive T3<R>(E: Events, F: Events) {{ Ret3(r: R), Vis3(c: E.Cmd, k: E.Resp(c) -> T3<R>(F, E)) }}"
    ));
    assert!(m.contains("`T3<R>(E, F)`"), "{m}");
    // A declaration with no value parameters applied to one: the argument is
    // an index or a parameter, and the message says which is which.
    let m = bad("inductive D { E, F(x: D(0)) }");
    assert!(m.contains("declares no value parameters"), "{m}");
}

/// An index beside value parameters (on the `IWf` route since
/// issues/indexed-families-at-any-index-type.md): an occurrence writes the
/// value parameters and then the index, and one that leaves the index out,
/// or varies a value argument, is refused by name.
#[test]
fn an_index_beside_value_parameters() {
    ok("inductive D(m: Nat) : (n: Nat) -> Type { E : D(m, 0), F(k: Nat, d: D(m, k)) : D(m, Succ(k)) }
        fn e3() -> D(3, 0) { E }
        fn f3() -> D(3, 1) { F(0, E) }");
    let m = bad("inductive D(m: Nat) : (n: Nat) -> Type { E : D(0) }");
    assert!(m.contains("with no index after its value parameters"), "{m}");
    let m = bad("inductive D(m: Nat) : (n: Nat) -> Type { E : D(m, 0), F(k: Nat, d: D(Succ(m), k)) : D(m, Succ(k)) }");
    assert!(m.contains("at value arguments other than its own value parameters"), "{m}");
}

/// The other refusals: a field that would shadow a parameter in *any*
/// constructor, not only the first.
#[test]
fn the_declaration_refusals_carry_their_messages() {
    let m = bad("inductive D(m: Nat) { E, F(m: Nat) }");
    assert!(m.contains("a value parameter of `D` and a field of its constructor `F`"), "{m}");
    let m = bad("inductive D(m: Nat) { E(x: Nat), F(y: Nat, m: Nat) }");
    assert!(m.contains("constructor `F`"), "{m}");
    // A record keeps its own, field-naming, message.
    let m = bad("record R(f: Nat) { f: Nat }");
    assert!(m.contains("both a value parameter and a field"), "{m}");
    // …and a record that mentions itself uniformly is still an `inductive`.
    let m = bad("record R(m: Nat) { x: R(m) }");
    assert!(m.contains("a recursive declaration is an `inductive`"), "{m}");
}

// -- 7: inference position reads the parameter off the arguments -----------

/// issues/value-param-constructor-implicit-inference.md: where nothing checks
/// a construction, its value parameters are solved as a call's implicits are,
/// by unifying each field's type with its argument's. `W`'s field is another
/// value-parameterised declaration (`Float::Fin(f)` at `f : Finite(F)`), `P`'s
/// a proposition (`Float::Inf(b, h)`), and `N` has nothing to read.
/// `Wrap::at` returns the parameter itself, so every `refl` against `m` is the
/// observer that the solution is the argument's and not a captured binder's.
const WRAP: &str = r#"
inductive Wrap(m: Nat) { W(w: Witness(m)), P(n: Nat, h: dbl(n) = m), N }
fn Wrap::get({m: Nat}, x: Wrap(m)) -> Nat { match x { W(w) => w.n, P(n, _) => n, N => 0 } }
fn Wrap::at({m: Nat}, x: Wrap(m)) -> Nat { m }
"#;

#[test]
fn inference_position_reads_the_parameter_off_a_field() {
    ok(&format!(
        r#"
        {BASE}
        {WRAP}
        theorem by_record(m: Nat, w: Witness(m)): Wrap::get(W(w)) = w.n {{ refl }}
        theorem by_evidence(m: Nat, n: Nat, h: dbl(n) = m): Wrap::get(P(n, h)) = n {{ refl }}
        theorem at_record(m: Nat, w: Witness(m)): Wrap::at(W(w)) = m {{ refl }}
        theorem at_evidence(m: Nat, n: Nat, h: dbl(n) = m): Wrap::at(P(n, h)) = m {{ refl }}
        theorem at_literal(h: dbl(2) = 4): Wrap::at(P(2, h)) = 4 {{ refl }}
        theorem lit_get(w: Witness(4)): Wrap::get(W(w)) = w.n {{ refl }}
        fn let_bound(m: Nat, n: Nat, h: dbl(n) = m) -> Nat {{ let x = P(n, h); x.get() }}
        theorem let_bound_is(m: Nat, n: Nat, h: dbl(n) = m): let_bound(m, n, h) = n {{ refl }}
        theorem nested(m: Nat, n: Nat, h: dbl(n) = m): Wrap::at(W(Witness(n, h))) = m {{ refl }}
        theorem record_too(m: Nat, n: Nat, h: dbl(n) = m): Witness(n, h).n = n {{ refl }}
        "#
    ));
    // The observer has teeth: the parameter is `m`, not anything else.
    let m = bad(&format!(
        "{BASE}\n{WRAP}\ntheorem t(m: Nat, w: Witness(m)): Wrap::at(W(w)) = Succ(m) {{ refl }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

/// An open element type beside the parameter (`A` from `a`, then `m` from
/// `h`), a child-only constructor (the child's type is the whole instance),
/// and tier 2: `Tau(t)` reads its instance off the child, while `Ret(r)` has
/// nothing that fixes `E` and says so.
#[test]
fn inference_position_with_type_parameters_children_and_tier_2() {
    ok(&format!(
        r#"
        {BASE}
        inductive Bag<A>(m: Nat) {{ Nil0, Put(a: A, n: Nat, h: dbl(n) = m, rest: Bag<A>(m)) }}
        fn bag_m<A>({{m: Nat}}, b: Bag<A>(m)) -> Nat {{ m }}
        theorem bag<A>(m: Nat, a: A, n: Nat, h: dbl(n) = m, rest: Bag<A>(m)):
            bag_m(Put(a, n, h, rest)) = m {{ refl }}
        inductive Ch(m: Nat) {{ Lf(w: Witness(m)), Br2(l: Ch(m), r: Ch(m)) }}
        fn ch_m({{m: Nat}}, c: Ch(m)) -> Nat {{ m }}
        theorem child(m: Nat, l: Ch(m), r: Ch(m)): ch_m(Br2(l, r)) = m {{ refl }}
        theorem both(m: Nat, w: Witness(m)): ch_m(Br2(Lf(w), Lf(w))) = m {{ refl }}
        "#
    ));
    ok(&format!(
        r#"
        {ITREE}
        fn ev_of<R>({{E: Events}}, t: ITree<R>(E)) -> Events {{ E }}
        theorem tau<R>(E: Events, t: ITree<R>(E)): ev_of(Tau(t)) = E {{ refl }}
        "#
    ));
    let m = bad(&format!("{ITREE}\nfn f(r: Nat) -> Nat {{ let t = Ret(r); 0 }}"));
    assert!(m.contains("cannot infer the value argument `E` of `ITree`"), "{m}");
}

/// The negative controls: two fields that disagree about the parameter are
/// a type error at the second (the construction is re-checked at the
/// solution), and a field that would fix the parameter but whose argument
/// only checks is named in the refusal.
#[test]
fn inference_position_refusals() {
    let m = bad(&format!(
        r#"
        {BASE}
        inductive Pr(m: Nat) {{ Pr2(a: Witness(m), b: Witness(m)) }}
        fn pr_m({{m: Nat}}, x: Pr(m)) -> Nat {{ m }}
        fn f(m: Nat, a: Witness(m), b: Witness(Succ(m))) -> Nat {{ pr_m(Pr2(a, b)) }}
        "#
    ));
    assert!(m.contains("but `Witness(m)` is expected"), "{m}");
    let m = bad(&format!(
        "{BASE}\nfn two_m({{m: Nat}}, t: Two(m)) -> Nat {{ m }}\nfn f() -> Nat {{ two_m(A(2, refl)) }}"
    ));
    assert!(m.contains("cannot infer the value argument `m` of `Two`"), "{m}");
    assert!(m.contains("its field `h` would"), "{m}");
    // The call's own note suggests the spelling that works for a value
    // implicit — by name — and not `<…>`, which is refused for one.
    assert!(m.contains("`two_m(m := …, …)`"), "{m}");
    assert!(!m.contains("two_m<"), "{m}");
}

