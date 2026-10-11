//! Type-owned members, receiver half: `fn D::m(…)` attaches a declaration to
//! `D`'s namespace, and `t.m(a)` reaches it through the receiver's type.
//! Tracking issue: `issues/type-owned-members-receiver-slice.md`.
//!
//! Two things are under test and they fail differently. The **attachment** is
//! checked at the declaration (a qualifier that names no type is an error
//! there, not a mystery at the use). The **reachability** is receiver-directed
//! and must never race candidates: where both an ambient name and a member
//! could be meant, the answer is an ambiguity, because preferring the member
//! would let a library addition silently reinterpret existing text.

use heather_elab::{ElabError, Elaborator};

fn run(mods: &[(&str, &str)]) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in mods {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

/// The library shape this slice exists for: a tier-1 polymorphic type and a
/// member that is curried in its second argument, so a receiver call needs
/// [[call-site-overapplication]] too (`xs.nth(i)` is `List::nth(xs)(i)`).
const LIST: &str = r#"
inductive Option<A> { None, Some(v: A) }
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }

fn List::nth<A>(self xs: List<A>) -> Nat -> Option<A> {
    match xs {
        Nil => λ (i: Nat) => None,
        Cons(h, t) => λ (i: Nat) => match i { Zero => Some(h), Succ(k) => nth(t)(k) },
    }
}
"#;

// -- 1: the attachment ----------------------------------------------------

#[test]
fn a_member_declaration_is_reachable_by_qualification() {
    ok(&format!(
        "{LIST} fn at<A>(xs: List<A>, i: Nat) -> Option<A> {{ List::nth(xs, i) }}"
    ));
}

// A member may recurse under its base name — inside `fn List::nth` the call is
// `nth(t)`. Already exercised by `LIST` itself; asserted here so this spelling
// stays available alongside the qualified one.
#[test]
fn a_member_recurses_under_its_base_name() {
    ok(&format!("{LIST} fn probe<A>(xs: List<A>) -> Nat {{ 0 }}"));
}

// The fully qualified declaration head is an alias for the in-progress
// self-reference, not a provisionally published global. This is especially
// useful for type-valued members, whose uses naturally read as qualified
// predicates.
#[test]
fn a_member_recurses_under_its_qualified_name() {
    ok("fn Nat::Even(n: Nat) -> Type {
            match n {
                Zero => True,
                Succ(k) => Nat::Even(k),
            }
        }");
}

// The alias must take the guarded self-call path. If it fell through ordinary
// global resolution, this would either be an unknown qualifier or an
// unrestricted recursive global call.
#[test]
fn a_qualified_self_call_is_still_structurally_guarded() {
    let e = bad("fn Nat::loop(n: Nat) -> Nat { Nat::loop(n) }");
    assert!(e.contains("not structurally guarded"), "{e}");
}

// The base name does **not** enter the ambient namespace: that is the
// shrinking half of the design, not an accident.
#[test]
fn a_members_base_name_is_not_ambient() {
    let e = bad(&format!(
        "{LIST} fn at<A>(xs: List<A>, i: Nat) -> Option<A> {{ nth(xs, i) }}"
    ));
    assert!(e.contains("unbound name `nth`"), "{e}");
}

// The attachment is checked, which is the difference between this and a Lean
// naming convention.
#[test]
fn a_member_of_a_type_that_does_not_exist_is_rejected_at_the_declaration() {
    // The owner rule admits a type *former* as well as a type as of 2026-08-17
    // (`docs/decide-class-design.md` §2.3), so the message names both. An
    // undeclared name is neither, and is refused on the path it always was.
    let e = bad("fn Frobnicate::x(n: Nat) -> Nat { n }");
    assert!(e.contains("not a type"), "{e}");
    assert!(e.contains("Frobnicate"), "{e}");
}

// `Nat` is a kernel type with no declaration, and it still owns a namespace:
// the parent design's `Nat::cong` has to be spellable eventually.
#[test]
fn a_kernel_type_owns_a_namespace_too() {
    ok("fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
        fn Nat::double(self n: Nat) -> Nat { add(n, n) }
        theorem d(n: Nat): n.double() = add(n, n) { refl }");
}

// -- 2: reachability through the receiver ---------------------------------

#[test]
fn a_receiver_reaches_its_types_member() {
    ok(&format!(
        "{LIST} fn at<A>(xs: List<A>, i: Nat) -> Option<A> {{ xs.nth(i) }}"
    ));
}

// The receiver spelling and the qualified one are the *same term*, not two
// well-typed ones: checked as a proof, so the kernel compares them.
#[test]
fn the_receiver_spelling_is_the_qualified_one() {
    ok(&format!(
        "{LIST}
         theorem same<A>(xs: List<A>, i: Nat): xs.nth(i) = List::nth(xs, i) {{ refl }}"
    ));
}

// Axis 3 (docs/testing-generated-terms.md): a **checking** position at a
// neutral receiver, where the result type must convert with a goal rather
// than be computed away.
#[test]
fn a_receiver_call_works_in_checking_position_at_a_neutral_receiver() {
    // Literal head, neutral tail, open element type, and a *proof* — the
    // annotation has to convert with the goal rather than be reduced away.
    ok(&format!(
        "{LIST}
         theorem step<A>(h: A, t: List<A>, i: Nat):
             Cons(h, t).nth(Succ(i)) = t.nth(i) {{ refl }}
         theorem here<A>(h: A, t: List<A>): Cons(h, t).nth(0) = Some(h) {{ refl }}"
    ));
}

// The `self` marker decides which argument slot the receiver fills, exactly as
// for a bare method call — resolved against the *qualified* name, which is the
// one place this could have quietly regressed.
#[test]
fn the_self_marker_still_places_the_receiver() {
    ok("inductive Box { Mk(v: Nat) }
        fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
        fn Box::shift(n: Nat, self b: Box) -> Nat { match b { Mk(v) => add(v, n) } }
        theorem s(): Mk(2).shift(3) = 5 { refl }");
}

// -- 3: negative controls -------------------------------------------------

// A member's base name that is *also* an ambient name, at a receiver whose
// type owns the member: an ambiguity naming both, never a silent preference.
// This is the growth-invariant control — with a preference, adding `D::m` to a
// library would reinterpret every existing `t.m(…)`.
#[test]
fn an_ambient_name_and_a_member_at_the_same_receiver_are_ambiguous() {
    let e = bad(&format!(
        "{LIST}
         fn nth<A>(xs: List<A>, i: Nat) -> Option<A> {{ None }}
         fn at<A>(xs: List<A>, i: Nat) -> Option<A> {{ xs.nth(i) }}"
    ));
    assert!(e.contains("List::nth"), "{e}");
    assert!(e.contains("both"), "{e}");
}

// The declaration currently being checked is in scope under its base name so
// that it can recurse. It is not a competing method when its own receiver has
// a known, different carrier from the written receiver.
#[test]
fn an_in_progress_member_of_another_type_does_not_shadow_the_receiver_member() {
    ok("inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
        inductive Box<A> { Mk(contents: List<A>) }
        fn List::size<A>(self xs: List<A>) -> Nat {
            match xs { Nil => 0, Cons(_, tail) => Succ(size(tail)) }
        }
        fn Box::size<A>(self b: Box<A>) -> Nat {
            match b { Mk(contents) => contents.size() }
        }");
}

// Carrier filtering only removes a provably inapplicable self-reference. A
// declaration whose receiver has the same carrier remains a genuine second
// reading, just like an already committed ambient declaration.
#[test]
fn an_applicable_in_progress_name_still_competes_with_the_receiver_member() {
    let e = bad("fn Nat::value(self n: Nat) -> Nat { n }
        fn value(n: Nat) -> Nat { n.value() }");
    assert!(e.contains("both `Nat::value`"), "{e}");
}

// A receiver whose type owns no such member: the ordinary unbound-name error
// on the base name, i.e. the pre-member behaviour of the method fallback.
#[test]
fn a_receiver_without_the_member_falls_back_to_the_bare_name() {
    let e = bad(&format!(
        "{LIST} fn at<A>(xs: List<A>) -> Nat {{ xs.nosuch() }}"
    ));
    assert!(e.contains("unbound name `nosuch`"), "{e}");
}

// A member of *another* type is not reachable from this receiver: membership
// is by the receiver's type and nothing else.
#[test]
fn a_member_of_another_type_is_not_reachable() {
    let e = bad(&format!(
        "{LIST}
         fn at<A>(o: Option<A>, i: Nat) -> Option<A> {{ o.nth(i) }}"
    ));
    assert!(e.contains("unbound name `nth`"), "{e}");
}

// Record fields still win over members at the same name: field resolution is
// the first test in `resolve_dot` and this slice must not have moved it.
#[test]
fn a_record_field_still_beats_a_member_of_the_same_name() {
    ok("record Pair { fst: Nat, snd: Nat }
        fn Pair::fst(self p: Pair) -> Nat { 0 }
        fn read(p: Pair) -> Nat { p.fst }");
}

// Membership crosses module boundaries by the ordinary regime: the member is
// declared in the module that declares the type, and an importer reaches it
// through a receiver without qualifying anything.
#[test]
fn a_member_is_reachable_across_modules() {
    run(&[
        ("list", LIST),
        (
            "user",
            "import list;\n\
             fn at<A>(xs: List<A>, i: Nat) -> Option<A> { xs.nth(i) }\n\
             fn at2<A>(xs: List<A>, i: Nat) -> Option<A> { List::nth(xs, i) }",
        ),
    ])
    .expect("a member crosses a module boundary like any other name");
}

// Two modules attaching the same member to the same type are ambiguous at the
// use, with both origins named — the §4 regime, inherited rather than
// re-implemented.
#[test]
fn two_modules_attaching_the_same_member_are_ambiguous() {
    let e = match run(&[
        ("shape", "inductive P { Mk }"),
        ("a", "import shape;\nfn P::tag(self p: P) -> Nat { 1 }"),
        ("b", "import shape;\nfn P::tag(self p: P) -> Nat { 2 }"),
        ("user", "import shape;\nimport a;\nimport b;\nfn u(p: P) -> Nat { p.tag() }"),
    ]) {
        Err(e) => e,
        Ok(_) => panic!("two attachments of one member must be ambiguous at the use"),
    };
    assert!(e.contains("ambiguous"), "{e}");
    assert!(e.contains('a') && e.contains('b'), "{e}");
}

// -- 4: receivers that do not infer on their own --------------------------
//
// docs/receiver-member-resolution-design.md §1. `R::mk()` and `Nil` are not
// inferable alone — their implicit is solved by the use — yet the head names
// the owner. The owner only picks the qualified name; the desugared call,
// with the expected type in hand, decides whether it typechecks.

/// A record whose parameter only a use site can fix. The field `p` keeps
/// `n` recoverable from `R(n)`: a parameter no field mentions is not.
const REC: &str = r#"
record R(n: Nat) { x: Nat, p: x = n }
fn R::mk({n: Nat}) -> R(n) { R(x := n, p := refl) }
fn R::bump({n: Nat}, self r: R(n)) -> R(n) { r }
fn R::get({n: Nat}, self r: R(n)) -> Nat { r.x }
"#;

// Axis: a **checking** position pins the receiver's implicit through the
// member's result. Before this round: "unbound name `bump`".
#[test]
fn a_receiver_owned_by_its_head_reaches_the_member_in_checking_position() {
    ok(&format!("{REC} fn c(n: Nat) -> R(n) {{ R::mk().bump() }}"));
}

// The receiver spelling is the qualified one, as a term the kernel compares —
// in a **statement**, where nothing but the named argument fixes `n`.
#[test]
fn a_named_argument_pins_a_receiver_in_a_statement() {
    ok(&format!(
        "{REC} theorem t(n: Nat): R::mk(n := n).bump() = R::bump(R::mk(n := n)) {{ refl }}"
    ));
}

// The receiver of a method chain: the outer receiver `R::mk().bump()` is
// itself a method call, owned by the result of the member it resolves to.
// Pinned by a named argument, the chain checks as a term equal to the
// qualified spelling.
#[test]
fn the_receiver_of_a_method_chain_is_owned_by_the_inner_members_result() {
    ok(&format!(
        "{REC} theorem t(n: Nat): R::mk(n := n).bump().bump() = R::bump(R::bump(R::mk(n := n))) {{ refl }}"
    ));
    // Pinned only by the goal, the chain reaches `R::bump` at both levels
    // and checks as the qualified spelling does: the nested uninferable
    // argument waits for its domain
    // (issues/nested-uninferable-argument-under-checking.md).
    for body in ["R::mk().bump().bump()", "R::bump(R::bump(R::mk()))"] {
        ok(&format!("{REC} fn c(n: Nat) -> R(n) {{ {body} }}"));
    }
    // Pinned by nothing, both spellings still report the call that owns the
    // width, never an unbound name.
    for body in ["R::get(R::mk().bump().bump())", "R::get(R::bump(R::bump(R::mk())))"] {
        let e = bad(&format!("{REC} fn c() -> Nat {{ {body} }}"));
        assert!(e.contains("could not infer the implicit argument `n` of `R::mk`"), "{e}");
        assert!(!e.contains("unbound name"), "{e}");
    }
}

// Deep chains would duplicate the entire prefix at every method call. Count
// actual receiver inferences rather than relying on a wall-clock threshold.
fn measured_chain(src: &str) -> (Result<(), String>, u64, u64) {
    use heather_elab::stats::{self, Counter, ScopeKind};
    let mut e = Elaborator::with_prelude().expect("prelude");
    stats::enable();
    let scope = stats::scope(ScopeKind::Run, "chain", "");
    let result = e.elab_source(src).map_err(|err| err.render(src));
    drop(scope);
    let rows = stats::take_rows();
    stats::disable();
    let row = rows.iter().find(|r| r.kind == ScopeKind::Run).unwrap();
    (result, row.counters[Counter::DotReceiverInferences as usize],
        row.counters[Counter::DotReceiverReuses as usize])
}

#[test]
fn inferable_method_chains_reuse_each_receiver() {
    for depth in [8, 28] {
        let chain = ".bump()".repeat(depth);
        for receiver in ["r", "R::mk(n := n)"] {
            let src = format!("{REC} fn c(n: Nat, r: R(n)) -> R(n) {{ {receiver}{chain} }}");
            let (result, inferred, reused) = measured_chain(&src);
            result.unwrap();
            assert_eq!(inferred, (depth - 1) as u64);
            assert!(reused >= inferred, "each inferred prefix must be reused: {reused}/{inferred}");
        }
    }
    let depth = 12;
    let chain = ".bump(n := n)".repeat(depth);
    let (result, inferred, reused) = measured_chain(&format!(
        "{REC} fn c(n: Nat, r: R(n)) -> R(n) {{ r{chain} }}"
    ));
    result.unwrap();
    assert_eq!(inferred, (depth - 1) as u64);
    assert!(reused >= inferred);

    let chain = ".stay()".repeat(depth);
    ok(&format!("{LIST}
        fn List::stay<A>(self xs: List<A>) -> List<A> {{ xs }}
        fn c<A>(xs: List<A>) -> List<A> {{ xs{chain} }}"));
}

#[test]
fn failed_receiver_inference_is_reused_but_checking_can_still_pin_it() {
    let depth = 20;
    let chain = ".bump()".repeat(depth);
    let src = format!("{REC} fn c() -> Nat {{ R::mk(){chain}.get() }}");
    let (result, inferred, reused) = measured_chain(&src);
    let error = result.unwrap_err();
    assert!(error.contains("could not infer the implicit argument `n` of `R::mk`"), "{error}");
    assert!(!error.contains("unbound name"), "{error}");
    assert_eq!(inferred, depth as u64, "each failed prefix is inferred once");
    assert!(reused > 0);

    ok(&format!("{REC} fn c(n: Nat) -> R(n) {{ R::mk(){chain} }}"));
    let error = bad(&format!("{REC} fn c(n: Nat, r: R(n)) -> R(Succ(n)) {{ r{chain} }}"));
    assert!(
        error.contains("this has type `R(n)`, but `R(Succ(n))` is expected here"),
        "an incompatible result must still fail: {error}"
    );
}

// A constructor with no written type arguments names its inductive: the gate
// on written type arguments is lifted on this path. `Nil` at an **open**
// element type reaches `List::rev` and, like `List::rev(Nil)`, waits for the
// declared result to pin `A` (issues/nullary-ctor-argument-not-deferred.md).
// The control: with nothing to pin it, both fail the same honest way — not as
// an unbound name.
#[test]
fn a_bare_constructor_receiver_names_its_inductive() {
    for body in ["Nil.rev()", "List::rev(Nil)"] {
        ok(&format!(
            "{LIST}
             fn List::rev<A>(self xs: List<A>) -> List<A> {{ xs }}
             fn e<A>() -> List<A> {{ {body} }}"
        ));
        let e = bad(&format!(
            "{LIST}
             fn List::rev<A>(self xs: List<A>) -> List<A> {{ xs }}
             fn e() -> Nat {{ let x = {body}; 0 }}"
        ));
        assert!(e.contains("cannot infer the type argument `A` of `List`"), "{e}");
        assert!(!e.contains("unbound name"), "{e}");
    }
}

// Genuinely unpinned: the honest failure of the desugared call, with the
// spelling that fixes it, and never "unbound name".
#[test]
fn an_unpinned_receiver_reports_its_implicit_with_the_named_spelling() {
    let e = bad(&format!("{REC} fn u() -> Nat {{ R::mk().get() }}"));
    assert!(e.contains("could not infer the implicit argument `n` of `R::mk`"), "{e}");
    assert!(e.contains("R::mk(n := …)"), "{e}");
    assert!(!e.contains("unbound name"), "{e}");
}

// Negative control: a head that is a **local** says nothing about the owner —
// the local `mk` shadows the global of that name, whose result is an `R`, and
// its implicit leaves the receiver uninferable — so the call falls back to
// the bare name, as before this round. The global head is the control.
#[test]
fn a_receiver_headed_by_a_local_still_falls_back_to_the_bare_name() {
    let prefix = format!("{REC} fn mk({{n: Nat}}) -> R(n) {{ R::mk() }}");
    let e = bad(&format!("{prefix} fn u(mk: {{n: Nat}} -> R(n)) -> Nat {{ mk().get() }}"));
    assert!(e.contains("unbound name `get`"), "{e}");
    let e = bad(&format!("{prefix} fn u() -> Nat {{ mk().get() }}"));
    assert!(e.contains("could not infer the implicit argument `n` of `mk`"), "{e}");
}

// -- 5: ambient readings that cannot take the receiver --------------------
//
// docs/receiver-member-resolution-design.md §2. An ambient reading is dropped
// only when it provably cannot typecheck at this receiver; anything less is
// still the ambiguity of
// `an_ambient_name_and_a_member_at_the_same_receiver_are_ambiguous`.

// An ambient global whose subject is a `Nat`, at an `R` receiver — and the
// call is the member, as a term.
#[test]
fn an_ambient_global_with_a_disjoint_subject_does_not_block_the_member() {
    ok(&format!(
        "{REC}
         fn get(k: Nat) -> Nat {{ k }}
         theorem t(n: Nat, r: R(n)): r.get() = R::get(r) {{ refl }}"
    ));
}

// A `let` alias that is not a function at all: `len` is a `Nat` here.
#[test]
fn a_local_that_is_not_a_function_does_not_block_the_member() {
    ok(&format!(
        "{LIST}
         fn add(a: Nat, b: Nat) -> Nat {{ match b {{ Zero => a, Succ(k) => Succ(add(a, k)) }} }}
         fn List::len<A>(self xs: List<A>) -> Nat {{
             match xs {{ Nil => 0, Cons(_, t) => Succ(len(t)) }}
         }}
         fn l(xs: List<Nat>, ys: List<Nat>) -> Nat {{ let len = xs.len(); add(len, ys.len()) }}"
    ));
}

// A local function whose first explicit parameter is a `Nat`.
#[test]
fn a_local_function_with_a_disjoint_subject_does_not_block_the_member() {
    ok(&format!("{REC} fn l(n: Nat, get: Nat -> Nat, r: R(n)) -> Nat {{ r.get() }}"));
}

// The same filter on the class-dispatch race: a bare `op` over `Nat` is no
// rival to `Mag<Z>`'s `op` at a `Z` receiver (before: "both").
#[test]
fn an_ambient_global_with_a_disjoint_subject_does_not_race_a_class_member() {
    ok("class Mag<A> { op: A -> A -> A }
        inductive Z { Z0, Z1 }
        instance Mag<Z> { fn op(x: Z, y: Z) -> Z { y } }
        fn op(x: Nat, y: Nat) -> Nat { x }
        theorem f(a: Z, b: Z) : a.op(b) = b { refl }");
}

// Negative control: a **generic** subject can take any receiver, so the
// ambiguity stands.
#[test]
fn an_ambient_global_with_a_generic_subject_stays_ambiguous() {
    let e = bad(&format!(
        "{REC}
         fn get<A>(self a: A) -> Nat {{ 0 }}
         fn u(n: Nat, r: R(n)) -> Nat {{ r.get() }}"
    ));
    assert!(e.contains("both `R::get`"), "{e}");
}

// Negative control: the **same** carrier is a real second reading.
#[test]
fn an_ambient_global_with_the_same_carrier_stays_ambiguous() {
    let e = bad(&format!(
        "{REC}
         fn get({{n: Nat}}, r: R(n)) -> Nat {{ 0 }}
         fn u(n: Nat, r: R(n)) -> Nat {{ r.get() }}"
    ));
    assert!(e.contains("both `R::get`"), "{e}");
}

// Negative control: a local whose subject is an open type variable stays a
// rival too.
#[test]
fn a_local_function_with_an_open_subject_stays_ambiguous() {
    let e = bad(&format!("{REC} fn l<A>(n: Nat, get: A -> Nat, r: R(n)) -> Nat {{ r.get() }}"));
    assert!(e.contains("both `R::get`"), "{e}");
}

// -- 6: diagnostics -------------------------------------------------------

// "declared below" is about the name that missed: a member `V::get` further
// down is not a bare `get`, and a member's base name is never ambient.
#[test]
fn a_member_declared_below_is_not_the_bare_name_declared_below() {
    let e = bad("inductive V { V0 }
        fn u(n: Nat) -> Nat { get(n) }
        fn V::get(self v: V) -> Nat { 0 }");
    assert!(e.contains("unbound name `get`"), "{e}");
    assert!(!e.contains("declared below"), "{e}");
    // Control: a bare `get` further down still gets the hint.
    let e = bad("fn u(n: Nat) -> Nat { get(n) }
        fn get(n: Nat) -> Nat { n }");
    assert!(e.contains("`get` is declared below"), "{e}");
}

/// issues/type-member-missing-self-diagnostic.md: the receiver is meant for
/// a later parameter, and the declaration forgot to mark it.
const UNMARKED: &str = r#"
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
record Failure<T>(source: List<T>) { at: Nat }
record View { at: Nat }
fn Failure::view<T>(source: List<T>, error: Failure<T>(source)) -> View { View(at := error.at) }
inductive Box { Mk(v: Nat) }
fn Box::shift(n: Nat, b: Box) -> Nat { n }
fn Box::two(n: Nat, a: Box, b: Box) -> Nat { n }
fn Box::fine(b: Box, n: Nat) -> Nat { n }
"#;

// The issue's shape: an implicit type argument, and a dependent value
// parameter before the intended receiver. Not "give the type arguments".
#[test]
fn a_missing_self_marker_is_named_for_a_generic_member() {
    let e = bad(&format!(
        "{UNMARKED} fn u<T>(source: List<T>, e: Failure<T>(source)) -> View {{ e.view(source) }}"
    ));
    assert!(e.contains("marks no parameter `self`"), "{e}");
    assert!(e.contains("self error:"), "{e}");
    assert!(!e.contains("type argument"), "{e}");
}

// Non-generic: here the mismatch is the kernel's, found at the gate, and the
// note at the receiver says the same thing.
#[test]
fn a_missing_self_marker_is_named_for_a_plain_member() {
    let e = bad(&format!("{UNMARKED} fn u(b: Box) -> Nat {{ b.shift(3) }}"));
    assert!(e.contains("self b: Box"), "{e}");
}

// Controls: an unmarked member whose receiver *is* its first parameter works;
// two candidate parameters, a qualified call and a bare global call never get
// the suggestion.
#[test]
fn the_missing_self_suggestion_is_narrow() {
    ok(&format!("{UNMARKED} fn u(b: Box) -> Nat {{ b.fine(3) }}"));
    let e = bad(&format!("{UNMARKED} fn u(b: Box) -> Nat {{ b.two(3, b) }}"));
    assert!(!e.contains("`self`"), "{e}");
    let e = bad(&format!("{UNMARKED} fn u(b: Box) -> Nat {{ Box::shift(b, 3) }}"));
    assert!(!e.contains("`self`"), "{e}");
    let e = bad(&format!(
        "{UNMARKED} fn shift(n: Nat, b: Box) -> Nat {{ n }}
         fn u(b: Box) -> Nat {{ shift(b, 3) }}"
    ));
    assert!(!e.contains("`self`"), "{e}");
}

// -- 7: a member declared at one instance of its type ---------------------
//
// issues/width-specific-method-on-other-width.md. The receiver's type selects
// `Word::low` by its name alone, so a member declared for `Word(8)` is reached
// from every `Word(n)`; the kernel refuses the wrong one, and the note names
// the member and both instances instead of two types that displayed as `Word`.

const WORD: &str = r#"
record Word(n: Nat) { cells: [Nat; n] }
fn Word::low(self w: Word(8)) -> Word(8) { w }
"#;

#[test]
fn a_member_at_one_value_argument_takes_a_receiver_at_that_argument() {
    ok(&format!("{WORD} fn u(x: Word(8)) -> Word(8) {{ x.low() }}"));
}

#[test]
fn a_receiver_at_another_value_argument_is_named_with_both_instances() {
    let e = bad(&format!("{WORD} fn u(x: Word(16)) -> Word(8) {{ x.low() }}"));
    assert!(
        e.contains("`Word::low` takes a receiver of type `Word(8)`, but this receiver has type `Word(16)`"),
        "{e}"
    );
}

// An open argument: the width is a variable, and the note spells it.
#[test]
fn a_receiver_at_an_open_value_argument_is_named_too() {
    let e = bad(&format!("{WORD} fn u(m: Nat, x: Word(m)) -> Word(8) {{ x.low() }}"));
    assert!(e.contains("this receiver has type `Word(m)`"), "{e}");
}

// Not a receiver: the same mismatch at a plain argument, and at a member's
// result, gets the ordinary note — which now shows the arguments it differs in.
#[test]
fn a_value_argument_mismatch_elsewhere_is_spelled_with_its_arguments() {
    let e = bad(&format!(
        "{WORD} fn low(w: Word(8)) -> Word(8) {{ w }}
         fn u(x: Word(16)) -> Word(8) {{ low(x) }}"
    ));
    assert!(e.contains("this has type `Word(16)`, but `Word(8)` is expected here"), "{e}");
    assert!(!e.contains("takes a receiver"), "{e}");
    let e = bad(&format!("{WORD} fn u(x: Word(8)) -> Word(16) {{ x.low() }}"));
    assert!(e.contains("this has type `Word(8)`, but `Word(16)` is expected here"), "{e}");
    assert!(!e.contains("takes a receiver"), "{e}");
}

// -- Function-owned members ------------------------------------------------
//
// A `fn` owns a namespace too (issues/function-owned-members.md): a fact about
// one function is named under it, `theorem f::name(…)`, and reached by
// qualification. The receiver never reaches it — `f.name` dispatches on the
// type of `f`, a function type with no namespace.

const DOUBLE: &str = r#"
fn double(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(Succ(double(k))) } }
theorem double::zero(): double(0) = 0 { refl }
"#;

#[test]
fn a_function_member_is_declared_and_reached_by_qualification() {
    ok(&format!("{DOUBLE} theorem u(): double(0) = 0 {{ double::zero() }}"));
}

// A function member may itself be a function, called like any other.
#[test]
fn a_function_owns_a_function_member() {
    ok("fn double(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(Succ(double(k))) } }
        fn double::twice(n: Nat) -> Nat { double(double(n)) }
        theorem u(): double::twice(1) = 4 { refl }");
}

// The member's statement is checked, not just its name: a use at the wrong
// goal is the ordinary mismatch, and the qualified name is what is reported.
#[test]
fn a_function_member_is_named_in_full_in_diagnostics() {
    let e = bad(&format!("{DOUBLE} theorem u(): double(0) = 0 {{ double::zero(1) }}"));
    assert!(e.contains("`double::zero` is applied to too many arguments"), "{e}");
    let e = bad(&format!("{DOUBLE} theorem double::zero(): double(0) = 0 {{ refl }}"));
    assert!(e.contains("duplicate name `double::zero`"), "{e}");
}

// The base name stays out of the ambient namespace, exactly as a type's
// member's does.
#[test]
fn a_function_members_base_name_is_not_in_scope() {
    let e = bad(&format!("{DOUBLE} theorem u(): double(0) = 0 {{ zero() }}"));
    assert!(e.contains("unbound name `zero`"), "{e}");
}

// `double.zero()` cannot reach it, and with no ambient `zero` the refusal says
// which spelling does.
#[test]
fn a_dot_call_on_a_function_names_the_qualified_member() {
    let e = bad(&format!("{DOUBLE} theorem u(): double(0) = 0 {{ double.zero() }}"));
    assert!(e.contains("the member of the function `double` is `double::zero(…)`"), "{e}");
}

// A function member and a type's member with the same base name are two
// declarations: each qualification reaches its own, and the receiver reaches
// the type's.
#[test]
fn a_function_member_and_a_same_named_type_member_stay_distinct() {
    ok("record Pt { x: Nat }
        fn Pt::zero(self p: Pt) -> Nat { 7 }
        fn double(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(Succ(double(k))) } }
        theorem double::zero(): double(0) = 0 { refl }
        theorem by_fn(): double(0) = 0 { double::zero() }
        theorem by_ty(p: Pt): Pt::zero(p) = 7 { refl }
        theorem by_recv(p: Pt): p.zero() = 7 { refl }");
}

#[test]
fn a_function_member_is_reached_from_an_importer() {
    let src = "fn double(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(Succ(double(k))) } }
               theorem double::zero(): double(0) = 0 { refl }";
    for user in [
        "import d;\ntheorem u(): double(0) = 0 { double::zero() }",
        "import d;\ntheorem u(): d::double(0) = 0 { d::double::zero() }",
    ] {
        if let Err(e) = run(&[("d", src), ("user", user)]) {
            panic!("{user}: {e}");
        }
    }
    // A facade reexports it like a type's member, by its qualified name.
    run(&[
        ("d", src),
        ("f", "export d::{double, double::zero};"),
        ("user", "import f;\ntheorem u(): double(0) = 0 { double::zero() }"),
    ])
    .unwrap_or_else(|e| panic!("{e}"));
}

// Two modules attaching the same member to the same function are ambiguous at
// the use, as for a type's member — and qualification by module resolves it.
#[test]
fn two_modules_attaching_one_function_member_are_ambiguous() {
    let mods = |user: &'static str| {
        run(&[
            ("d", "fn double(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(Succ(double(k))) } }"),
            ("a", "import d;\ntheorem double::zero(): double(0) = 0 { refl }"),
            ("b", "import d;\ntheorem double::zero(): double(0) = 0 { refl }"),
            ("user", user),
        ])
    };
    let e = match mods("import d;\nimport a;\nimport b;\ntheorem u(): double(0) = 0 { double::zero() }") {
        Ok(_) => panic!("expected an ambiguity"),
        Err(e) => e,
    };
    assert!(e.contains("ambiguous"), "{e}");
    mods("import d;\nimport a;\nimport b;\ntheorem u(): double(0) = 0 { a::double::zero() }")
        .unwrap_or_else(|e| panic!("{e}"));
}

// The owner rule's refusals: a theorem owns nothing, and neither does a name
// that is not declared (yet).
#[test]
fn a_theorem_or_an_unknown_owner_is_refused() {
    let e = bad("theorem t(): 0 = 0 { refl } theorem t::again(): 0 = 0 { refl }");
    assert!(e.contains("`t` is a theorem, so `t::again` attaches to nothing"), "{e}");
    let e = bad("theorem later::zero(): 0 = 0 { refl } fn later(n: Nat) -> Nat { n }");
    assert!(e.contains("not a type, a type former or a function in scope"), "{e}");
}

// `f::name` reads as the module `f`'s `name` first, so a function named like a
// visible module cannot own members — the declaration is refused rather than
// left unreachable.
#[test]
fn a_function_named_like_a_visible_module_owns_no_members() {
    let e = match run(&[
        ("m", "fn other(n: Nat) -> Nat { n }"),
        ("user", "import m;\nfn m(n: Nat) -> Nat { n }\ntheorem m::id(): m(0) = 0 { refl }"),
    ]) {
        Ok(_) => panic!("expected a refusal"),
        Err(e) => e,
    };
    assert!(e.contains("would read as `id` in the module `m`"), "{e}");
}

// And across modules, where the declaring module could not see the clash: a
// client that sees both the module `f` declaring `name` and a member `f::name`
// gets an ambiguity, never a silent pick — so the module growing a `name`
// cannot reinterpret a member reference.
#[test]
fn a_module_path_and_a_function_member_spelled_alike_are_ambiguous() {
    let mods = |user: &'static str| {
        run(&[
            ("sq", "fn zero() -> Nat { 0 }"),
            ("d", "fn sq(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => sq(k) } }\ntheorem sq::zero(): sq(0) = 0 { refl }"),
            ("user", user),
        ])
    };
    let e = match mods("import sq;\nimport d;\ntheorem u(): d::sq(0) = 0 { sq::zero() }") {
        Ok(_) => panic!("expected an ambiguity"),
        Err(e) => e,
    };
    assert!(e.contains("`sq::zero` is ambiguous"), "{e}");
    assert!(e.contains("`d::sq::zero`"), "{e}");
    mods("import sq;\nimport d;\ntheorem u(): d::sq(0) = 0 { d::sq::zero() }")
        .unwrap_or_else(|e| panic!("{e}"));
}
