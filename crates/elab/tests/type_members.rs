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

// A member recurses under its base name — inside `fn List::nth` the call is
// `nth(t)`. Already exercised by `LIST` itself; asserted here so the reason
// is written down where it can fail.
#[test]
fn a_member_recurses_under_its_base_name() {
    ok(&format!("{LIST} fn probe<A>(xs: List<A>) -> Nat {{ 0 }}"));
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
