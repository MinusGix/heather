//! Acceptance for indexed families, **route 2b** — the fording generator, end
//! to end (`docs/inductive-fording-lowering.md` §13.2 items 8–14; the hand
//! prototype behind it is `indexed_route_2b_wf.rs`, and the fording *layer*'s
//! acceptance is `indexed_route_2b.rs`).
//!
//! Every declaration below is lowered to `Σ(s : Skel). sEq(I; μ s; m)` and
//! re-checked by the real kernel, so a wrong encoding is a rejection rather
//! than a checked theorem about the wrong type. The axes are
//! `docs/testing-generated-terms.md`'s, and each test names the ones it
//! carries:
//!
//! - **axis 1** — a *literal* scrutinee asserted to **compute** (a `refl`
//!   theorem against the written reduct), not merely to typecheck;
//! - **axis 2** — a *neutral* scrutinee, and an **open** element type (`<A>`
//!   instantiated at a variable, and a `Type`-valued field at level 1);
//! - **axis 3** — a **checking** position: every claim below is a `theorem`,
//!   which is a checking position across the index equation;
//! - **axis 4** — a **negative control** per encoding decision: F1, F2 and F3
//!   each have one, the uniform-parameter row has one, and §8.4's form-B
//!   residue has one (a *deliberate* negative, so the gap is in a test rather
//!   than in a bug report).

use heather_elab::{ElabError, Elaborator, IndexedRoute};
use heather_kernel::term::{GlobalBinding, Term, Type};

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

const ADD: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
"#;

// ---------------------------------------------------------------------------
// §13.2 item 8 — the classifier
// ---------------------------------------------------------------------------

// §3.3's rows, each with its own message. Axis 4 for every encoding decision
// F1–F3 rests on: each of these declarations *would* lower to something under
// a weaker classifier, and what it would lower to is a quotient of the family
// the user wrote (§4.2, and the prototype's `f2_falsifier_…`).
#[test]
fn f1_a_child_at_a_non_variable_index_rejects() {
    // `l`'s index is the constant `0`: fording recomputes a child's index from
    // the child, so a constructor may only pin it by *naming* it.
    let m = elab_err(&format!(
        "{ADD}
         inductive B1 : (n: Nat) -> Type {{
             B1Z                                      : B1(0),
             B1N(n: Nat, l: B1(0), r: B1(n))          : B1(add(n, n)),
         }}"
    ));
    assert!(m.contains("is not a variable"), "{m}");
    assert!(m.contains("coherence predicate"), "{m}");
}

#[test]
fn f2_two_children_at_one_index_rejects() {
    // The skeleton cannot record that two children agree — a label cannot
    // mention its children — so the constraint would need §10.3's predicate.
    let m = elab_err(&format!(
        "{ADD}
         inductive B2 : (n: Nat) -> Type {{
             B2Z                                      : B2(0),
             B2N(n: Nat, l: B2(n), r: B2(n))          : B2(add(n, n)),
         }}"
    ));
    assert!(m.contains("share the index variable `n`"), "{m}");
    assert!(m.contains("coherence predicate"), "{m}");
}

#[test]
fn f3_a_payload_depending_on_a_child_index_rejects() {
    // `x`'s type mentions `n`, which fords away: `n` is recomputed from `xs`,
    // and a child is not in scope in a payload field's type.
    let m = elab_err(&format!(
        "{ADD}
         inductive B3 : (n: Nat) -> Type {{
             B3Z                                      : B3(0),
             B3C(n: Nat, x: Fin(n), xs: B3(n))        : B3(add(n, n)),
         }}"
    ));
    assert!(m.contains("fords away"), "{m}");
    assert!(m.contains("route-1-eligible if every result index is a pattern"), "{m}");
}

#[test]
fn a_uniform_bare_variable_index_is_still_a_parameter() {
    // §3.3's first row, unchanged: route 2b would happily generate this, so
    // the route-1 message has to win rather than be tried after.
    let m = elab_err("inductive Q : (n: Nat) -> Type { Mk(n: Nat) : Q(n) }");
    assert!(m.contains("a **parameter**, not an index"), "{m}");
    assert!(m.contains("record Q(n: Nat)"), "{m}");
}

#[test]
fn the_mixed_row_names_both_constructors() {
    // §3.3's mixed row: `MA` is not route-1-eligible (a deep pattern) and `MB`
    // is not route-2b-eligible (F2), so the declaration is in neither
    // fragment — and saying only one is what sends a user in a circle.
    let m = elab_err(
        "inductive MX : (n: Nat) -> Type {
             MA(n: Nat, p: MX(n))                     : MX(Succ(Succ(n))),
             MB(n: Nat, l: MX(n), r: MX(n))           : MX(n),
         }",
    );
    assert!(m.contains("in neither indexed fragment"), "{m}");
    assert!(m.contains("`MA` is not route-1-eligible"), "{m}");
    assert!(m.contains("`MB` is not route-2b-eligible"), "{m}");
    assert!(m.contains("deeper than one constructor"), "{m}");
    assert!(m.contains("share the index variable"), "{m}");
}

// §3.4's worked examples, each routed where §3 says. The route-1 rows keep
// their old behaviour verbatim (`indexed_families.rs` owns their β); the rest
// are new arrivals, and the tests below carry them one at a time.
#[test]
fn every_worked_example_routes_where_section_three_says() {
    // Route 1, unchanged: a pattern result index with children at pattern
    // variables still lowers by recursion on the index.
    let one = elab(
        "inductive V<A> : (n: Nat) -> Type {
             VNil                                     : V<A>(0),
             VCons(n: Nat, x: A, xs: V<A>(n))         : V<A>(Succ(n)),
         }
         fn three() -> V<Nat>(3) { VCons(2, 1, VCons(1, 2, VCons(0, 3, VNil))) }",
    );
    assert_eq!(one.indexed_route("V"), Some(IndexedRoute::One));
    // Computed result index (the motivating class), deep pattern, branching
    // with a computed index, and a non-uniform bare variable: all route 2b.
    let forded = elab(&format!(
        "{ADD}
         inductive Tm : (n: Nat) -> Type {{
             Lit                                      : Tm(Succ(0)),
             Ap(n: Nat, m: Nat, f: Tm(n), a: Tm(m))   : Tm(add(n, m)),
         }}
         inductive Ev : (n: Nat) -> Type {{
             EZ                                       : Ev(0),
             ESS(n: Nat, p: Ev(n))                    : Ev(Succ(Succ(n))),
         }}
         inductive Br : (n: Nat) -> Type {{
             BL                                       : Br(0),
             BN(n: Nat, m: Nat, l: Br(n), r: Br(m))   : Br(Succ(add(n, m))),
         }}
         inductive Any : (n: Nat) -> Type {{
             AZ                                       : Any(0),
             AA(n: Nat)                               : Any(n),
         }}"
    ));
    for name in ["Tm", "Ev", "Br", "Any"] {
        assert_eq!(
            forded.indexed_route(name),
            Some(IndexedRoute::Forded),
            "worked example `{name}` took the wrong indexed route"
        );
    }
}

// ---------------------------------------------------------------------------
// §13.2 item 9 — the `Term`/`App`-shaped declaration, end to end
// ---------------------------------------------------------------------------

const TM: &str = r#"
inductive Tm : (n: Nat) -> Type {
    Lit                                          : Tm(Succ(0)),
    Ap(n: Nat, m: Nat, f: Tm(n), a: Tm(m))       : Tm(add(n, m)),
}
fn size(n: Nat, t: Tm(n)) -> Nat {
    match t { Lit => 1, Ap(a, b, f, x) => add(size(a, f), size(b, x)) }
}
"#;

#[test]
fn term_app_declares_constructs_matches_and_proves() {
    // Axes 1, 2 and 3 together: a literal scrutinee that *computes*, a neutral
    // one at an open index that types, and both in checking position.
    elab(&format!(
        "{ADD}{TM}
         fn one() -> Tm(1) {{ Lit }}
         fn two() -> Tm(2) {{ Ap(1, 1, Lit, Lit) }}
         // Axis 2: construction at **open** indices, over open children.
         fn app(n: Nat, m: Nat, f: Tm(n), a: Tm(m)) -> Tm(add(n, m)) {{ Ap(n, m, f, a) }}
         // Axis 1: the eliminator computes on literal data.
         theorem size_lit(): size(1, Lit) = 1 {{ refl }}
         theorem size_two(): size(2, two()) = 2 {{ refl }}
         // Axis 3: a checking position across the equation — `Tm(2)` and
         // `Tm(add(1, 1))` are the same type, and the value passes **bare**
         // (§9 rule 1: no re-indexing coercion, ever).
         fn two_spelled() -> Tm(add(1, 1)) {{ two() }}
         theorem two_bare(): size(add(1, 1), two_spelled()) = 2 {{ refl }}"
    ));
}

#[test]
fn a_recursive_theorem_over_the_forded_family() {
    // A `theorem` over the forded family, by `match`, with the self-call in the
    // recursive `fn` beneath it rebound to the arm's own index (§12.2:
    // `Guard.rebind` carries one index term per descendant, `μ(child_t)` rather
    // than a pattern variable).
    //
    // Note what this theorem is *not*: a full induction with a `j` at the `Ap`
    // step. Both of `Tm`'s constructors are form B (`Succ(0)` is not a variable
    // pattern and `add(n, m)` is not a pattern at all), so §8.4's third bullet
    // applies to every arm — a constructor over an open child carries a
    // non-`srefl` proof, the arm's `transp` does not β, and the residue is a
    // stuck `App(transp …)`. The form-A induction that *does* close is
    // `a_theorem_by_induction_whose_step_is_a_form_a_constructor_closes`; this
    // is the honest boundary between them, in a test rather than in a comment.
    elab(&format!(
        "{ADD}{TM}
         theorem size_by_cases(n: Nat, t: Tm(n)): size(n, t) = size(n, t) {{
             match t {{ Lit => refl, Ap(a, b, f, x) => refl }}
         }}
         theorem size_two_ways(n: Nat, t: Tm(n)): add(size(n, t), 0) = size(n, t) {{
             match t {{ Lit => refl, Ap(a, b, f, x) => refl }}
         }}
         // …and the recursion itself, on literal data, through both arms.
         theorem deep(): size(3, Ap(2, 1, Ap(1, 1, Lit, Lit), Lit)) = 3 {{ refl }}"
    ));
}

// ---------------------------------------------------------------------------
// §13.2 item 10 — the branching forded `Tree`
// ---------------------------------------------------------------------------

const TREE: &str = r#"
inductive Tree<A> : (n: Nat) -> Type {
    Leaf                                                : Tree<A>(0),
    Bud(n: Nat, x: A, t: Tree<A>(n))                    : Tree<A>(Succ(n)),
    Node(n: Nat, m: Nat, l: Tree<A>(n), r: Tree<A>(m))  : Tree<A>(Succ(add(n, m))),
}
fn count<A>(n: Nat, t: Tree<A>(n)) -> Nat {
    match t {
        Leaf => 0,
        Bud(k, x, s) => Succ(count(k, s)),
        Node(a, b, l, r) => Succ(add(count(a, l), count(b, r))),
    }
}
"#;

#[test]
fn branching_tree_end_to_end() {
    // The `Wf`-skeleton composition (§10.1), generated: `Leaf` and `Bud` are
    // route-1-eligible on their own and get §8.2's inversion; `Node`'s index
    // `Succ(add(n, m))` is not a pattern and gets §8.3's `transp`. One
    // eliminator, both forms.
    //
    // Axis 2 twice over: the element type is the **open** `A` of a polymorphic
    // `fn`, and the scrutinee is neutral.
    elab(&format!(
        "{ADD}{TREE}
         fn leaf() -> Tree<Nat>(0) {{ Leaf }}
         fn small() -> Tree<Nat>(1) {{ Bud(0, 7, Leaf) }}
         fn pair2() -> Tree<Nat>(1) {{ Node(0, 0, Leaf, Leaf) }}
         fn build<A>(n: Nat, m: Nat, x: A, l: Tree<A>(n), r: Tree<A>(m))
             -> Tree<A>(Succ(Succ(add(n, m)))) {{ Bud(Succ(add(n, m)), x, Node(n, m, l, r)) }}
         // Axis 1: literal scrutinees that compute, through both arm forms.
         theorem c_leaf(): count(0, leaf()) = 0 {{ refl }}
         theorem c_bud(): count(1, small()) = 1 {{ refl }}
         theorem c_node(): count(1, pair2()) = 1 {{ refl }}"
    ));
}

#[test]
fn form_a_beta_is_definitional_on_open_data() {
    // §8.2's rule, generated and measured: `Bud` would have been
    // route-1-eligible on its own, so its arm inverts the *motive's* index and
    // the stored proof is consulted nowhere — β fires with the element, the
    // subtree and the index all open, at an **open element type**.
    elab(&format!(
        "{ADD}{TREE}
         fn tleaf() -> Tree<Nat>(0) {{ Leaf }}
         theorem bud_beta(n: Nat, x: Nat, t: Tree<Nat>(n)):
             count(Succ(n), Bud(n, x, t)) = Succ(count(n, t)) {{ refl }}
         theorem leaf_beta(): count(0, tleaf()) = 0 {{ refl }}
         // Axis 2, the open element type: the same β, stated as a polymorphic
         // `fn` whose result *is* the equation, so `A` comes from the binder
         // rather than from inference through a polymorphic call.
         fn bud_beta_open<A>(n: Nat, x: A, t: Tree<A>(n))
             -> count(Succ(n), Bud(n, x, t)) = Succ(count(n, t)) {{ refl }}"
    ));
}

#[test]
fn form_b_beta_stalls_on_open_children_and_this_is_the_documented_residue() {
    // §8.4's third bullet, as a **deliberate negative**: a forded constructor
    // manufactures a non-`srefl` proof as soon as one of its children is open
    // (the proof is a `transp` chain over a variable), the arm's own `transp`
    // does not β, and the residue is a stuck `App(transp …)` that the
    // head-only strip never reaches
    // (`docs/metatheory-ch07-extensions.md` §22.1 in a new position).
    //
    // The consequence is bounded and stated: a spurious `NotConvertible` at
    // check time, never an unsound accept. This test is where that is visible
    // rather than in a bug report — and it is `count`'s *only* failing claim,
    // which is what makes it residue and not a defect.
    //
    // Written without the `tnode` wrapper since 2026-08-04: `Node(n, m, l, r)`
    // now infers its instantiation from a child (§14.7), so the claim is the
    // constructor's own and the residue cannot be blamed on the wrapper.
    let m = elab_err(&format!(
        "{ADD}{TREE}
         theorem node_beta(n: Nat, m: Nat, l: Tree<Nat>(n), r: Tree<Nat>(m)):
             count(Succ(add(n, m)), Node(n, m, l, r))
                 = Succ(add(count(n, l), count(m, r))) {{ refl }}"
    ));
    // The shape of the failure is the claim: a kernel `NotConvertible`, not a
    // wrong answer and not a loop.
    assert!(m.contains("NotConvertible"), "{m}");
}

// ---------------------------------------------------------------------------
// §14.7 — type-argument inference for forded constructors
// ---------------------------------------------------------------------------

#[test]
fn a_child_argument_determines_the_instantiation() {
    // The seam as recorded (2026-08-04): `Node` carries no field whose surface
    // type is a bare parameter, so `infer_ctor` could not solve `A` and the
    // *common* forded shape — only index and child fields — was unusable in
    // inference position. The way out is not a unifier: a child's type **is**
    // the family, at that child's own index, and both routes keep the family in
    // a form that re-applies at another index. So the instance comes back whole
    // and nothing is solved.
    //
    // Axis 2 throughout: the children, the indices and the element type are all
    // open, and `count<A>`'s own type argument is what the constructor's
    // inferred type then settles.
    elab(&format!(
        "{ADD}{TREE}
         fn c(n: Nat, m: Nat, l: Tree<Nat>(n), r: Tree<Nat>(m)) -> Nat {{
             count(Succ(add(n, m)), Node(n, m, l, r))
         }}
         theorem node_infers(n: Nat, m: Nat, l: Tree<Nat>(n), r: Tree<Nat>(m)):
             count(Succ(add(n, m)), Node(n, m, l, r))
                 = count(Succ(add(n, m)), Node(n, m, l, r)) {{ refl }}"
    ));
}

#[test]
fn an_undetermined_instantiation_is_rejected_and_names_both_escapes() {
    // `Leaf` has no arguments at all, so nothing determines `A` — that is
    // genuinely ambiguous and stays a rejection. What the round owes is a
    // message that names the two ways out, and both of them working.
    let m = elab_err(&format!("{ADD}{TREE} theorem t(): count(0, Leaf) = 0 {{ refl }}"));
    assert!(m.contains("cannot infer the type argument `A`"), "{m}");
    assert!(m.contains("checking position"), "{m}");
    assert!(m.contains("Leaf<…>"), "{m}");
    elab(&format!(
        "{ADD}{TREE}
         // Escape 1: a checking position.
         fn tleaf() -> Tree<Nat>(0) {{ Leaf }}
         theorem a(): count(0, tleaf()) = 0 {{ refl }}
         // Escape 2: the written type argument. New on 2026-08-04 — `ctor_at`
         // used to lower the *unindexed* instance, so `Leaf<Nat>` failed with
         // \"needs its index\"; the index is the constructor's own written
         // result index, exactly as in inference position.
         theorem b(): count(0, Leaf<Nat>) = 0 {{ refl }}
         fn bud() -> Tree<Nat>(1) {{ Bud<Nat>(0, 7, Leaf<Nat>) }}"
    ));
}

#[test]
fn conflicting_children_are_rejected() {
    // Axis 4 for the read-back: the instance comes from the *first* child, and
    // every other argument is then checked against it — so two children at
    // different instantiations reject rather than the second one being
    // silently coerced into the first.
    let m = elab_err(&format!(
        "{ADD}{TREE}
         inductive Col {{ CA, CB }}
         theorem t(n: Nat, m: Nat, l: Tree<Nat>(n), r: Tree<Col>(m)):
             count(Succ(add(n, m)), Node(n, m, l, r)) = 0 {{ refl }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

#[test]
fn a_theorem_by_induction_whose_step_is_a_form_a_constructor_closes() {
    // §13.2 item 10's positive half. The declaration fords — `NlD`'s index
    // `add(a, b)` is computed — but its *recursive* constructor `NlC` is
    // route-1-eligible on its own, so the induction's step arm gets form A's
    // definitional β and the `j` closes. That is §8.2's rule paying out: inside
    // 2b, a constructor computes exactly when it would have been
    // route-1-eligible on its own.
    elab(&format!(
        "{ADD}
         inductive Nl : (n: Nat) -> Type {{
             NlZ                                      : Nl(0),
             NlC(n: Nat, x: Nat, t: Nl(n))            : Nl(Succ(n)),
             NlD(a: Nat, b: Nat)                      : Nl(add(a, b)),
         }}
         fn nsize(n: Nat, t: Nl(n)) -> Nat {{
             match t {{ NlZ => 0, NlC(k, x, s) => Succ(nsize(k, s)), NlD(a, b) => 0 }}
         }}
         fn nsize2(n: Nat, t: Nl(n)) -> Nat {{
             match t {{ NlZ => 0, NlC(k, x, s) => add(nsize2(k, s), 1), NlD(a, b) => 0 }}
         }}
         theorem nsize_agrees(n: Nat, t: Nl(n)): nsize(n, t) = nsize2(n, t) {{
             match t {{
                 NlZ => refl,
                 NlC(k, x, s) => j(nsize_agrees(k, s),
                     \u{3bb} y q => Succ(nsize(k, s)) = Succ(y),
                     refl),
                 NlD(a, b) => refl,
             }}
         }}"
    ));
}

// ---------------------------------------------------------------------------
// §13.2 item 11 — the deep pattern, the route-1 rejection that is now generated
// ---------------------------------------------------------------------------

#[test]
fn the_deep_pattern_declares_and_computes() {
    // `ESS(n, p: Ev(n)) : Ev(Succ(Succ(n)))`. Route 1 rejects it as "deeper
    // than one constructor"; route 2b generates it with no special case at all
    // — `μ(ess p) = S (S (μ p))` — and its `match` β is form B (§8.3), because
    // the outer `Succ`'s argument is not a variable.
    elab(&format!(
        "{ADD}
         inductive Ev : (n: Nat) -> Type {{
             EZ                                       : Ev(0),
             ESS(n: Nat, p: Ev(n))                    : Ev(Succ(Succ(n))),
         }}
         fn half(n: Nat, e: Ev(n)) -> Nat {{
             match e {{ EZ => 0, ESS(k, p) => Succ(half(k, p)) }}
         }}
         fn four() -> Ev(4) {{ ESS(2, ESS(0, EZ)) }}
         // Axis 1: it computes.
         theorem half_zero(): half(0, EZ) = 0 {{ refl }}
         theorem half_four(): half(4, four()) = 2 {{ refl }}
         // Axis 2: neutral scrutinee, typed at an open index.
         fn h(n: Nat, e: Ev(n)) -> Nat {{ half(n, e) }}
         // Axis 3: a checking position across a convertible-not-equal index.
         fn four_spelled() -> Ev(Succ(Succ(2))) {{ four() }}
         theorem half_spelled(): half(Succ(Succ(2)), four_spelled()) = 2 {{ refl }}"
    ));
}

// ---------------------------------------------------------------------------
// §13.2 item 12 — the non-uniform bare-variable index
// ---------------------------------------------------------------------------

#[test]
fn a_non_uniform_bare_variable_index_declares() {
    // `AA(n) : Any(n)` beside `AZ : Any(0)` — 2b-eligible, `μ(aa n) = n`
    // reading the stored payload `n` (§3.4). The skeleton here is
    // **non-recursive**, so `μ` is tier 0's case tree rather than `elim_Wf`
    // and the eliminator is `idx_case_tree` at the fording motive — the other
    // half of §4.1's shape test, exercised.
    elab(&format!(
        "{ADD}
         inductive Any : (n: Nat) -> Type {{
             AZ                                       : Any(0),
             AA(n: Nat)                               : Any(n),
         }}
         fn az() -> Any(0) {{ AZ }}
         fn aa(n: Nat) -> Any(n) {{ AA(n) }}
         fn read(n: Nat, a: Any(n)) -> Nat {{ match a {{ AZ => 0, AA(k) => k }} }}
         theorem read_az(): read(0, AZ) = 0 {{ refl }}
         theorem read_aa(n: Nat): read(n, AA(n)) = n {{ refl }}"
    ));
    // …and the *uniform* case still rejects with the parameter message, which
    // is what makes the row above a distinction and not a blanket widening.
    let m = elab_err("inductive Q : (n: Nat) -> Type { Mk(n: Nat) : Q(n) }");
    assert!(m.contains("a **parameter**, not an index"), "{m}");
}

// ---------------------------------------------------------------------------
// §13.2 item 13 — a forded family in another declaration and as a result type
// ---------------------------------------------------------------------------

#[test]
fn a_forded_family_is_a_field_and_a_result_type() {
    // §6.2: the Σ is at `l ⊔ li` and **both components have codes**
    // (`TmSigma`, `TmSEq`), so a forded family may be a field of another
    // declaration — which route 1's families can also do and tier-2 encodings
    // could not.
    elab(&format!(
        "{ADD}{TM}
         inductive Boxed {{ MkBoxed(n: Nat, t: Tm(n)) }}
         fn box_it(n: Nat, t: Tm(n)) -> Boxed {{ MkBoxed(n, t) }}
         fn box_len(b: Boxed) -> Nat {{ match b {{ MkBoxed(n, t) => n }} }}
         fn box_size(b: Boxed) -> Nat {{ match b {{ MkBoxed(n, t) => size(n, t) }} }}
         theorem boxed_round(n: Nat, t: Tm(n)): box_len(box_it(n, t)) = n {{ refl }}
         theorem boxed_size(n: Nat, t: Tm(n)): box_size(box_it(n, t)) = size(n, t) {{ refl }}
         // …and as a `fn` result type, at an open and at a literal index.
         fn mk_ap(n: Nat, m: Nat, f: Tm(n), a: Tm(m)) -> Tm(add(n, m)) {{ Ap(n, m, f, a) }}
         fn mk_lit() -> Tm(1) {{ Lit }}"
    ));
}

// ---------------------------------------------------------------------------
// §13.2 item 14 — a nonzero level, and §9's structural walker
// ---------------------------------------------------------------------------

const LEVEL1: &str = r#"
inductive TL : (n: Nat) -> Type {
    TLNil                                             : TL(0),
    TLCons(n: Nat, a: Type, t: TL(n))                 : TL(Succ(n)),
    TLCat(n: Nat, m: Nat, l: TL(n), r: TL(m))         : TL(add(n, m)),
}
fn tlen(n: Nat, t: TL(n)) -> Nat {
    match t {
        TLNil => 0,
        TLCons(k, a, s) => Succ(tlen(k, s)),
        TLCat(a, b, l, r) => add(tlen(a, l), tlen(b, r)),
    }
}
"#;

#[test]
fn fields_above_level_zero() {
    // §6.2 and route 1 §10.5's lesson, not re-learned: a `Type`-valued payload
    // field puts the skeleton and the family at level 1 while the motive stays
    // at 0, so every `l ⊔ li` and `l ⊔ mlvl` that was silently `mlvl` at level
    // 0 is now a different level. A dropped join cannot hide here.
    elab(&format!(
        "{ADD}{LEVEL1}
         fn one_ty() -> TL(1) {{ TLCons(0, Nat, TLNil) }}
         fn two_ty() -> TL(2) {{ TLCat(1, 1, one_ty(), one_ty()) }}
         theorem tl_nil(): tlen(0, TLNil) = 0 {{ refl }}
         theorem tl_two(): tlen(2, two_ty()) = 2 {{ refl }}
         // Form A at level 1, on open recursive data.
         theorem tl_cons(n: Nat, a: Type, t: TL(n)):
             tlen(Succ(n), TLCons(n, a, t)) = Succ(tlen(n, t)) {{ refl }}"
    ));
}

// -- §9's structural walker -------------------------------------------------
//
// > **The generator never emits a `transp` at convertible endpoints — in
// > VALUE, INDEX or CODE position.**
//
// How a violation is caught has to be a *test*, not a promise. This walker
// runs over **every term the 2b generator emits** — the type and body of every
// global the sources below produce — and asserts:
//
//  1. no `Transp` occurs under a `Type::Vec { len }`, a `Type::Wf { arity }` or
//     a `Type::El { tm }` (§9 rule 4: index and code positions are cast-free by
//     construction; §22.4's kernel-side negatives are why that matters, and
//     they are cited from `issues/seq-strip-type-former-negatives.md` rather
//     than duplicated);
//  2. every `Transp` has endpoints the walker cannot prove convertible by
//     syntactic equality (§9 rule 1: a redundant cast is opaque to elimination;
//     rule 3 says the arm cast's endpoints `μ ŝ` and the *bound* `m'` do not
//     convert under any instantiation the generator can see).
//
// The walk is deliberately **exhaustive-by-panic**: a node form it does not
// know fails the test rather than being skipped, so the assertion cannot pass
// vacuously by walking past the interesting part of a term.

#[derive(Default)]
struct Walk {
    transps: usize,
}

impl Walk {
    fn tm(&mut self, t: &Term, former: bool) {
        match t {
            Term::Transp { ty, motive, lhs, rhs, proof, tm, .. } => {
                assert!(
                    !former,
                    "§9: a `transp` under a `Vec` length, a `Wf` arity or an `El` code — \
                     a canonical type would read as neutral (docs/sprop-design.md §5.4)"
                );
                assert!(
                    lhs != rhs,
                    "§9: a `transp` at syntactically equal endpoints is redundant, and a \
                     redundant cast is opaque to elimination"
                );
                self.transps += 1;
                self.ty(ty, former);
                self.ty(motive, former);
                for x in [lhs, rhs, proof, tm] {
                    self.tm(x, former);
                }
            }
            Term::Var(_) | Term::TmNat | Term::TmTy(_) | Term::Zero | Term::NatLit(_) => {}
            Term::TmUnit { .. } | Term::TmEmpty { .. } | Term::TmSEmpty { .. } => {}
            Term::Triv { .. } => {}
            Term::Succ(a) => self.tm(a, former),
            Term::TmPi { dom, cod, .. } => {
                self.tm(dom, former);
                self.tm(cod, former);
            }
            Term::TmSigma { fst, snd, .. } => {
                self.tm(fst, former);
                self.tm(snd, former);
            }
            Term::TmSum { lhs, rhs, .. } | Term::TmW { shape: lhs, pos: rhs, .. } => {
                self.tm(lhs, former);
                self.tm(rhs, former);
            }
            Term::TmId { ty, lhs, rhs, .. } | Term::TmSEq { ty, lhs, rhs, .. } => {
                for x in [ty, lhs, rhs] {
                    self.tm(x, former);
                }
            }
            Term::TmVec { elem, len, .. } => {
                self.tm(elem, former);
                self.tm(len, true);
            }
            Term::TmFin { len } => self.tm(len, true),
            Term::TmWf { shape, arity, .. } => {
                self.tm(shape, former);
                self.tm(arity, true);
            }
            Term::ElimNat { motive, base, step, scrut, .. } => {
                self.ty(motive, former);
                for x in [base, step, scrut] {
                    self.tm(x, former);
                }
            }
            Term::Refl { ty, tm, .. } | Term::SRefl { ty, tm, .. } => {
                self.ty(ty, former);
                self.tm(tm, former);
            }
            Term::J { ty, lhs, motive, case, rhs, proof, .. } => {
                self.ty(ty, former);
                self.ty(motive, former);
                for x in [lhs, case, rhs, proof] {
                    self.tm(x, former);
                }
            }
            Term::ElimSEmpty { motive, scrut, .. } | Term::ElimEmpty { motive, scrut, .. } => {
                self.ty(motive, former);
                self.tm(scrut, former);
            }
            Term::Pair { fst_ty, snd_ty, fst, snd, .. } => {
                self.ty(fst_ty, former);
                self.ty(snd_ty, former);
                self.tm(fst, former);
                self.tm(snd, former);
            }
            Term::Fst { fst_ty, snd_ty, pair, .. } | Term::Snd { fst_ty, snd_ty, pair, .. } => {
                self.ty(fst_ty, former);
                self.ty(snd_ty, former);
                self.tm(pair, former);
            }
            Term::Inl { lhs, rhs, val, .. } | Term::Inr { lhs, rhs, val, .. } => {
                self.ty(lhs, former);
                self.ty(rhs, former);
                self.tm(val, former);
            }
            Term::Case { lhs, rhs, motive, case_l, case_r, scrut, .. } => {
                for x in [lhs, rhs, motive] {
                    self.ty(x, former);
                }
                for x in [case_l, case_r, scrut] {
                    self.tm(x, former);
                }
            }
            Term::Sup { shape_ty, pos_ty, label, children, .. } => {
                self.ty(shape_ty, former);
                self.ty(pos_ty, former);
                self.tm(label, former);
                self.tm(children, former);
            }
            Term::ElimW { shape, pos, motive, step, scrut, .. } => {
                for x in [shape, pos, motive] {
                    self.ty(x, former);
                }
                self.tm(step, former);
                self.tm(scrut, former);
            }
            Term::Supf { shape, arity, label, children, .. } => {
                self.ty(shape, former);
                self.tm(arity, true);
                self.tm(label, former);
                self.tm(children, former);
            }
            Term::ElimWf { shape, arity, motive, step, scrut, .. } => {
                self.ty(shape, former);
                self.tm(arity, true);
                self.ty(motive, former);
                self.tm(step, former);
                self.tm(scrut, former);
            }
            Term::Lam { dom, body, .. } => {
                self.ty(dom, former);
                self.tm(body, former);
            }
            Term::App { fun, dom, cod, arg, .. } => {
                self.tm(fun, former);
                self.ty(dom, former);
                self.ty(cod, former);
                self.tm(arg, former);
            }
            Term::GlobalTm { subst, .. } => {
                for x in &subst.terms {
                    self.tm(x, former);
                }
            }
            other => panic!("the §9 walker does not know this node: {other:?}"),
        }
    }

    fn ty(&mut self, t: &Type, former: bool) {
        match t {
            Type::Nat | Type::Ty(_) => {}
            Type::Unit { .. } | Type::Empty { .. } | Type::SEmpty { .. } => {}
            Type::Pi { dom, cod, .. } | Type::Sigma { fst: dom, snd: cod, .. } => {
                self.ty(dom, former);
                self.ty(cod, former);
            }
            Type::Sum { lhs, rhs, .. } | Type::W { shape: lhs, pos: rhs, .. } => {
                self.ty(lhs, former);
                self.ty(rhs, former);
            }
            // §9's CODE position: an `El`'s code is where a `transp` makes a
            // canonical type read as neutral.
            Type::El { tm, .. } => self.tm(tm, true),
            Type::Id { ty, lhs, rhs, .. } | Type::SEq { ty, lhs, rhs, .. } => {
                self.ty(ty, former);
                self.tm(lhs, former);
                self.tm(rhs, former);
            }
            // §9's INDEX positions.
            Type::Vec { elem, len, .. } => {
                self.ty(elem, former);
                self.tm(len, true);
            }
            Type::Fin { len } => self.tm(len, true),
            Type::Wf { shape, arity, .. } => {
                self.ty(shape, former);
                self.tm(arity, true);
            }
            Type::GlobalTy { subst, .. } => {
                for x in &subst.terms {
                    self.tm(x, former);
                }
            }
            other => panic!("the §9 walker does not know this type: {other:?}"),
        }
    }
}

fn walk_emitted(src: &str) -> usize {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let base = e.psi().bindings.len();
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    let mut w = Walk::default();
    for b in e.psi().bindings.iter().skip(base) {
        match b {
            GlobalBinding::Tm { ty, body, .. } => {
                w.ty(ty, false);
                if let Some(t) = body {
                    w.tm(t, false);
                }
            }
            GlobalBinding::Ty { .. } | GlobalBinding::Ctx => {}
        }
    }
    w.transps
}

#[test]
fn the_cast_rule_holds_over_every_emitted_term() {
    // Run the walker on the whole acceptance surface: the `Term`/`App` family,
    // the branching `Tree` at an open element type, the deep pattern, the
    // non-recursive skeleton, the boxed field, and the level-1 family.
    let mut seen = 0usize;
    seen += walk_emitted(&format!(
        "{ADD}{TM}
         fn app(n: Nat, m: Nat, f: Tm(n), a: Tm(m)) -> Tm(add(n, m)) {{ Ap(n, m, f, a) }}
         inductive Boxed {{ MkBoxed(n: Nat, t: Tm(n)) }}
         fn box_it(n: Nat, t: Tm(n)) -> Boxed {{ MkBoxed(n, t) }}
         fn box_size(b: Boxed) -> Nat {{ match b {{ MkBoxed(n, t) => size(n, t) }} }}"
    ));
    seen += walk_emitted(&format!(
        "{ADD}{TREE}
         fn build<A>(n: Nat, m: Nat, x: A, l: Tree<A>(n), r: Tree<A>(m))
             -> Tree<A>(Succ(Succ(add(n, m)))) {{ Bud(Succ(add(n, m)), x, Node(n, m, l, r)) }}
         fn bud_beta_open<A>(n: Nat, x: A, t: Tree<A>(n))
             -> count(Succ(n), Bud(n, x, t)) = Succ(count(n, t)) {{ refl }}"
    ));
    seen += walk_emitted(&format!(
        "{ADD}
         inductive Ev : (n: Nat) -> Type {{
             EZ                                       : Ev(0),
             ESS(n: Nat, p: Ev(n))                    : Ev(Succ(Succ(n))),
         }}
         fn half(n: Nat, e: Ev(n)) -> Nat {{
             match e {{ EZ => 0, ESS(k, p) => Succ(half(k, p)) }}
         }}
         fn four() -> Ev(4) {{ ESS(2, ESS(0, EZ)) }}"
    ));
    seen += walk_emitted(&format!(
        "{ADD}
         inductive Any : (n: Nat) -> Type {{
             AZ                                       : Any(0),
             AA(n: Nat)                               : Any(n),
         }}
         fn read(n: Nat, a: Any(n)) -> Nat {{ match a {{ AZ => 0, AA(k) => k }} }}"
    ));
    seen += walk_emitted(&format!(
        "{ADD}{LEVEL1}
         fn one_ty() -> TL(1) {{ TLCons(0, Nat, TLNil) }}
         fn two_ty() -> TL(2) {{ TLCat(1, 1, one_ty(), one_ty()) }}"
    ));
    // The walk is only worth anything if it *found* the casts the generator is
    // supposed to emit: §7's `π_c` chains and §8.3's arm casts. Zero would mean
    // the sources above never reached a forded term.
    assert!(seen > 0, "the walker found no `transp` at all — it walked past the generator");
}

// ---------------------------------------------------------------------------
// Axis 6 at the **fording** eliminator's own case tree
// (`issues/dependent-motive-crossing-sweep.md`, 2026-08-05)
// ---------------------------------------------------------------------------

/// `a_non_uniform_bare_variable_index_declares` reaches `idx_case_tree` — the
/// non-recursive-skeleton half of §4.1's shape test — but at **two**
/// constructors and a closed payload, so its case tree has no inner node and
/// no annotation mentions an ambient variable. This is that path at the axis-6
/// crossing: **three** constructors (so there is an inner `Case`) × an open
/// payload on the *middle* one (so its summand annotations mention `A`).
///
/// The motive `Q(σ) = Π(m' : I). Π(sEq(I; μ σ; m')). M[m', ⟨σ, e'⟩]` mentions
/// `σ` in its `sEq` domain whatever the surface motive says, so the third
/// condition of the 2026-08-05 refinement is already met here by construction
/// — unlike tier 0's and `indexed_case_tree`'s, whose motives come from the
/// surface. The mis-shift this would catch is a kernel `LevelMismatch`.
///
/// `FdA`'s bare-variable index and `FdS`'s `Succ` of a *payload* variable both
/// decline route 1, so the declaration is genuinely forded, and no field is
/// recursive, so the skeleton is non-recursive and the eliminator is
/// `idx_case_tree` rather than `elim_Wf`.
///
/// Writing it needed a fix first — see
/// [`a_parameterized_family_over_a_non_recursive_skeleton_is_usable`].
#[test]
fn the_forded_case_trees_inner_injection_is_scoped_two_binders_deep() {
    elab(&format!(
        "{ADD}
         inductive Fd<A> : (n: Nat) -> Type {{
             FdZ                                      : Fd<A>(0),
             FdA(n: Nat, x: A)                        : Fd<A>(n),
             FdS(n: Nat)                              : Fd<A>(Succ(n)),
         }}
         fn readf<A>(d: A, n: Nat, t: Fd<A>(n)) -> A {{
             match t {{ FdZ => d, FdA(k, x) => x, FdS(k) => d }}
         }}
         // Axis 1/3: a literal index that computes, in a checking position.
         theorem readf_a<A>(d: A, n: Nat, x: A): readf(d, n, FdA(n, x)) = x {{ refl }}
         theorem readf_z<A>(d: A): readf(d, 0, FdZ) = d {{ refl }}
         // Axis 2: a neutral scrutinee at an open index, still well typed.
         fn thru<A>(d: A, n: Nat, t: Fd<A>(n)) -> A {{ readf(d, n, t) }}"
    ));
    // The controls. Three constructors at a **closed** payload…
    elab(&format!(
        "{ADD}
         inductive Fdn : (n: Nat) -> Type {{
             FdZ                                      : Fdn(0),
             FdA(n: Nat, x: Nat)                      : Fdn(n),
             FdS(n: Nat)                              : Fdn(Succ(n)),
         }}
         fn readn(n: Nat, t: Fdn(n)) -> Nat {{
             match t {{ FdZ => 0, FdA(k, x) => x, FdS(k) => 0 }}
         }}
         theorem readn_a(n: Nat, x: Nat): readn(n, FdA(n, x)) = x {{ refl }}"
    ));
    // …and an open payload at **two** constructors, where there is no inner
    // `Case`.
    elab(&format!(
        "{ADD}
         inductive Fd2<A> : (n: Nat) -> Type {{
             FdZ                                      : Fd2<A>(0),
             FdA(n: Nat, x: A)                        : Fd2<A>(n),
         }}
         fn read2<A>(d: A, n: Nat, t: Fd2<A>(n)) -> A {{
             match t {{ FdZ => d, FdA(k, x) => x }}
         }}
         theorem read2_a<A>(d: A, n: Nat, x: A): read2(d, n, FdA(n, x)) = x {{ refl }}"
    ));
}

/// A **parameterized** forded family whose skeleton is **non-recursive**, used
/// at all (2026-08-05, `issues/dependent-motive-crossing-sweep.md`).
///
/// `branching_tree_end_to_end` has `Tree<A>`, but every constructor of it has a
/// recursive field, so its skeleton is a `Wf` and the whole match goes through
/// `tel.spine`. `a_non_uniform_bare_variable_index_declares` has a
/// non-recursive skeleton, but `Any` is monomorphic. Nothing crossed the two,
/// and in the gap `μ`'s branch context re-lowered the skeleton at **no** type
/// arguments (`forded.rs::ctor_spine_at`), so a field spelled `A` was resolved
/// against a fresh instantiation that had never bound it. The leak was a
/// name-resolution message from inside the generator — `unknown type `A`` —
/// pointing at the *declaration*, on the first use of any constructor.
///
/// Two constructors and no `match` are enough: the failure is in `μ`, which is
/// built for the constructor.
#[test]
fn a_parameterized_family_over_a_non_recursive_skeleton_is_usable() {
    elab(&format!(
        "{ADD}
         inductive Fq<A> : (n: Nat) -> Type {{
             FqZ                                      : Fq<A>(0),
             FqA(n: Nat, x: A)                        : Fq<A>(n),
         }}
         // A constructor: this alone was the rejection.
         fn mk<A>(n: Nat, x: A) -> Fq<A>(n) {{ FqA(n, x) }}
         fn mkz<A>() -> Fq<A>(0) {{ FqZ }}
         // …and the eliminator over it, monomorphic and polymorphic.
         fn readm(d: Nat, n: Nat, t: Fq<Nat>(n)) -> Nat {{
             match t {{ FqZ => d, FqA(k, x) => x }}
         }}
         fn readp<A>(d: A, n: Nat, t: Fq<A>(n)) -> A {{
             match t {{ FqZ => d, FqA(k, x) => x }}
         }}
         theorem readm_a(n: Nat, x: Nat): readm(0, n, FqA(n, x)) = x {{ refl }}
         theorem readp_a<A>(d: A, n: Nat, x: A): readp(d, n, FqA(n, x)) = x {{ refl }}"
    ));
}
