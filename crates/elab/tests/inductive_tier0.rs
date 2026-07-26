//! Acceptance for tier-0 inductives (issues/inductive-compiler.md), against
//! the checklist of `docs/inductive-tier0-lowering.md` §9.
//!
//! The whole point of the tier: every declaration below is lowered to
//! sums-of-Σs and then re-checked by the *real kernel*, so a wrong encoding
//! shows up here as a rejection. The tests that matter most are the ones where
//! a plausible-but-wrong lowering would still typecheck — the dependent
//! motives (`neg_neg`, `rot3`) and the nominal separation (`no_confusion`).

use heather_elab::{ElabError, Elaborator};

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

const BOOL: &str = r#"
inductive Bool { True, False }

fn neg(b: Bool) -> Bool {
    match b { True => False, False => True }
}
"#;

// §9.1 — declarations, constructors and derived functions all kernel-check.
#[test]
fn bool_declares_and_computes() {
    elab(&format!(
        "{BOOL}
         theorem neg_true(): neg(True) = False {{ refl }}
         theorem neg_false(): neg(False) = True {{ refl }}"
    ));
}

// §9.2 — `match` β-reduces on each canonical constructor, at arities 0/1/2.
#[test]
fn match_beta_at_every_arity() {
    elab(
        r#"
        inductive Box { Wrap(Nat) }
        inductive Two { Mk(a: Nat, b: Nat) }
        inductive Flag { On, Off }

        fn unbox(b: Box) -> Nat { match b { Wrap(x) => x } }
        fn fst(p: Two) -> Nat { match p { Mk(a, b) => a } }
        fn snd(p: Two) -> Nat { match p { Mk(a, b) => b } }
        fn flag(f: Flag) -> Nat { match f { On => 1, Off => 0 } }

        theorem t0(): flag(On) = 1 { refl }
        theorem t1(): unbox(Wrap(4)) = 4 { refl }
        theorem t2a(): fst(Mk(2, 7)) = 2 { refl }
        theorem t2b(): snd(Mk(2, 7)) = 7 { refl }
        "#,
    );
}

// §9.3 — a variable scrutinee under a motive that genuinely varies per
// constructor. `neg_neg` needs the (synthesized) dependent motive; `rot3`
// needs the *nested* motive of §5.2 to be composed with the injection at
// depth 1, which is the lowering's most error-prone step.
#[test]
fn dependent_motive_over_a_variable_scrutinee() {
    elab(&format!(
        "{BOOL}
         theorem neg_neg(b: Bool): neg(neg(b)) = b {{
             match b {{ True => refl, False => refl }}
         }}"
    ));
    elab(
        r#"
        inductive Three { A, B, C }
        fn rot(t: Three) -> Three { match t { A => B, B => C, C => A } }
        theorem rot3(t: Three): rot(rot(rot(t))) = t {
            match t { A => refl, B => refl, C => refl }
        }
        "#,
    );
}

// The explicit `as z -> M` motive path, on an inductive rather than `Nat`.
#[test]
fn explicit_motive_on_an_inductive() {
    elab(&format!(
        "{BOOL}
         theorem neg_neg(b: Bool): neg(neg(b)) = b {{
             match b as z -> neg(neg(z)) = z {{ True => refl, False => refl }}
         }}"
    ));
}

// Type parameters are monomorphized (§2): the same declaration at `Nat` and at
// `Bool`, both used in one file.
#[test]
fn parameters_are_monomorphized() {
    elab(&format!(
        "{BOOL}
         inductive Option<A> {{ None, Some(A) }}

         fn or_else(d: Nat, o: Option<Nat>) -> Nat {{
             match o {{ None => d, Some(x) => x }}
         }}
         fn is_set(o: Option<Bool>) -> Bool {{
             match o {{ None => False, Some(b) => b }}
         }}

         theorem s1(): or_else(3, Some(5)) = 5 {{ refl }}
         theorem s2(): or_else(3, None) = 3 {{ refl }}
         theorem s3(): is_set(Some(True)) = True {{ refl }}
         theorem s4(): is_set(None) = False {{ refl }}"
    ));
}

// A later field's type mentions an earlier field — the reason the field spine
// is a Σ and not a product (§3.1).
#[test]
fn a_field_type_depends_on_an_earlier_field() {
    elab(
        r#"
        inductive Witness { Mk(n: Nat, p: n = n) }
        fn value(w: Witness) -> Nat { match w { Mk(n, p) => n } }
        theorem w1(): value(Mk(3, refl)) = 3 { refl }
        "#,
    );
}

// §9.6 — the two degenerate arities: one constructor (a record, no `+` at all)
// and none (`Empty`, so `match` is absurdity elimination).
#[test]
fn record_and_empty_round_trip() {
    elab(
        r#"
        inductive Box { Wrap(Nat) }
        inductive Void { }

        fn unbox(b: Box) -> Nat { match b { Wrap(x) => x } }
        fn rewrap(b: Box) -> Box { match b { Wrap(x) => Wrap(x) } }
        fn absurd(v: Void) -> Nat { match v { } }

        theorem r1(): unbox(rewrap(Wrap(9))) = 9 { refl }
        "#,
    );
}

// Nested constructors: the inner one is elaborated in checking position, at the
// type the outer one's field spine demands.
#[test]
fn constructors_nest() {
    elab(
        r#"
        inductive Option<A> { None, Some(A) }
        fn depth(o: Option<Option<Nat>>) -> Nat {
            match o { None => 0, Some(i) => match i { None => 1, Some(n) => n } }
        }
        theorem d0(): depth(None) = 0 { refl }
        theorem d1(): depth(Some(None)) = 1 { refl }
        theorem d2(): depth(Some(Some(7))) = 7 { refl }
        "#,
    );
}

// -- the nominal tag (§3.3, §9.8) -------------------------------------------

#[test]
fn structurally_identical_types_do_not_confuse() {
    // Both lower to `Unit + Unit` but for the tag, so without §3.3 this would
    // typecheck — a proof about a type the user never meant.
    let msg = elab_err(
        r#"
        inductive Bool { True, False }
        inductive Direction { Left, Right }
        theorem confuse(): True = Left { refl }
        "#,
    );
    assert!(msg.contains("Direction"), "{msg}");
}

#[test]
fn a_constructor_of_another_type_is_not_an_arm() {
    let msg = elab_err(
        r#"
        inductive Bool { True, False }
        inductive Direction { Left, Right }
        fn f(b: Bool) -> Nat { match b { True => 1, Left => 0 } }
        "#,
    );
    assert!(msg.contains("not a constructor of `Bool`"), "{msg}");
}

// -- surface obligations the lowering relies on -----------------------------

#[test]
fn a_missing_arm_is_rejected() {
    let msg = elab_err(
        "inductive Three { A, B, C } fn f(t: Three) -> Nat { match t { A => 0, C => 2 } }",
    );
    assert!(msg.contains("missing an arm for `B`"), "{msg}");
}

#[test]
fn a_duplicate_arm_is_rejected() {
    let msg = elab_err(
        "inductive Bool { True, False }
         fn f(b: Bool) -> Nat { match b { True => 0, True => 1, False => 2 } }",
    );
    assert!(msg.contains("duplicate arm"), "{msg}");
}

#[test]
fn wrong_pattern_arity_is_rejected() {
    let msg = elab_err(
        "inductive Two { Mk(a: Nat, b: Nat) } fn f(p: Two) -> Nat { match p { Mk(a) => a } }",
    );
    assert!(msg.contains("binds 2 field(s)"), "{msg}");
}

#[test]
fn wrong_constructor_arity_is_rejected() {
    let msg = elab_err(
        "inductive Two { Mk(a: Nat, b: Nat) } fn f() -> Two { Mk(1) }",
    );
    assert!(msg.contains("takes 2 argument(s)"), "{msg}");
}

// §9.7 — a recursive declaration is *classified*, not silently lowered as if
// it were tier 0. A direct, uniform occurrence is now tier 1 and lowers onto
// the `Wf` former (docs/inductive-tier1-wf-lowering.md,
// crates/elab/tests/inductive_tier1.rs); everything else is still a rejection
// with its own message, and this is where that boundary is pinned.
#[test]
fn a_recursive_declaration_is_classified_not_lowered() {
    // Direct and uniform: tier 1, and it is not lowered as a sum-of-Σs.
    let e = elab("inductive List { Nil, Cons(Nat, List) } fn f(l: List) -> Nat { 0 }");
    drop(e);
    // Nested inside another type's arguments: rejected, not mis-lowered.
    let msg = elab_err(
        "inductive Option<A> { None, Some(A) }
         inductive Tree { Leaf, Node(Option<Tree>) }",
    );
    assert!(msg.contains("nested"), "{msg}");
}

#[test]
fn an_uninferable_instantiation_asks_for_an_annotation() {
    // A parametric constructor with nothing checking it: `None` alone cannot
    // determine `A`, and saying so beats guessing.
    let msg = elab_err(
        "inductive Option<A> { None, Some(A) }
         theorem t(): None = None { refl }",
    );
    assert!(msg.contains("cannot infer the type argument `A`"), "{msg}");
}

#[test]
fn name_clashes_are_rejected() {
    assert!(elab_err(
        "inductive A { X } inductive B { X }"
    )
    .contains("already a constructor"));
    assert!(elab_err("inductive Bool { True, Zero }").contains("built in"));
    assert!(elab_err("inductive Bool { True } inductive Bool { False }").contains("duplicate"));
}

// A local binder shadows a constructor name, as any other name would.
#[test]
fn a_local_shadows_a_constructor() {
    elab(
        r#"
        inductive Flag { On, Off }
        fn f(On: Nat) -> Nat { On }
        theorem t(): f(3) = 3 { refl }
        "#,
    );
}

// -- no-confusion (§6, checklist items 4 and 5) -----------------------------

// §9.4 — disjointness, for every ordered pair of distinct constructors,
// including the paths through the last one.
#[test]
fn distinct_constructors_are_provably_distinct() {
    elab(
        r#"
        inductive Three { A, B, C }
        theorem ab(p: A = B): 0 = 1 { absurd(p) }
        theorem ba(p: B = A): 0 = 1 { absurd(p) }
        theorem ac(p: A = C): 0 = 1 { absurd(p) }
        theorem ca(p: C = A): 0 = 1 { absurd(p) }
        theorem bc(p: B = C): 0 = 1 { absurd(p) }
        theorem cb(p: C = B): 0 = 1 { absurd(p) }
        "#,
    );
    // With fields, and through the method spelling.
    elab(
        r#"
        inductive Option<A> { None, Some(A) }
        theorem sn(n: Nat, p: Some(n) = None): 0 = 1 { p.absurd() }
        "#,
    );
}

// §9.5 — injectivity, including a two-field constructor field by field.
#[test]
fn constructors_are_injective() {
    elab(
        r#"
        inductive Option<A> { None, Some(A) }
        inductive Two { Mk(a: Nat, b: Nat) }

        theorem some_inj(a: Nat, b: Nat, p: Some(a) = Some(b)): a = b { inj(p) }
        theorem mk_fst(a: Nat, b: Nat, c: Nat, d: Nat, p: Mk(a, b) = Mk(c, d)): a = c {
            inj(0, p)
        }
        theorem mk_snd(a: Nat, b: Nat, c: Nat, d: Nat, p: Mk(a, b) = Mk(c, d)): b = d {
            inj(1, p)
        }
        "#,
    );
}

// Injectivity composes with the rest of the language: the derived equation is
// an ordinary proof term.
#[test]
fn injectivity_composes_with_other_lemmas() {
    elab(
        r#"
        inductive Option<A> { None, Some(A) }
        theorem some_inj_sym(a: Nat, b: Nat, p: Some(a) = Some(b)): b = a { inj(p).sym() }
        "#,
    );
}

#[test]
fn no_confusion_rejects_the_wrong_shape() {
    // `absurd` on an equation between the *same* constructor is not absurd…
    let msg = elab_err(
        "inductive Flag { On, Off } theorem t(p: On = On): 0 = 1 { absurd(p) }",
    );
    assert!(msg.contains("not absurd"), "{msg}");
    // …and `inj` between *different* ones is not injectivity.
    let msg = elab_err(
        "inductive Flag { On, Off } theorem t(p: On = Off): 0 = 1 { inj(p) }",
    );
    assert!(msg.contains("different constructors"), "{msg}");
    // A field index past the end.
    let msg = elab_err(
        "inductive Option<A> { None, Some(A) }
         theorem t(a: Nat, b: Nat, p: Some(a) = Some(b)): a = b { inj(3, p) }",
    );
    assert!(msg.contains("no field 3"), "{msg}");
    // Both sides have to be constructor applications.
    let msg = elab_err(
        "inductive Flag { On, Off } theorem t(x: Flag, p: x = On): 0 = 1 { absurd(p) }",
    );
    assert!(msg.contains("constructor applications"), "{msg}");
}

#[test]
fn a_dependent_field_reports_the_documented_limitation() {
    let msg = elab_err(
        "inductive Witness { Mk(n: Nat, p: n = n) }
         theorem t(a: Nat, b: Nat, pa: a = a, pb: b = b, e: Mk(a, pa) = Mk(b, pb)): a = b {
             inj(1, e)
         }",
    );
    assert!(msg.contains("depends on an earlier field"), "{msg}");
}

// The first field of a dependent constructor is still injective: only the
// *later* fields are out of reach.
#[test]
fn the_independent_field_of_a_dependent_constructor_is_injective() {
    elab(
        r#"
        inductive Witness { Mk(n: Nat, p: n = n) }
        theorem t(a: Nat, b: Nat, pa: a = a, pb: b = b, e: Mk(a, pa) = Mk(b, pb)): a = b {
            inj(0, e)
        }
        "#,
    );
}

// §3.1 — a type parameter instantiated at a *context-dependent* type
// (issues/tyvar-scoping-in-lowered-fields.md). The instantiation is lowered
// in the ambient context and then used under the nominal tag and the earlier
// fields, so each use has to be weakened by exactly that many binders.
//
// This is the observer the suite lacked: every other instantiation here is at
// a closed type, where the weakening is a no-op and a missing one is
// invisible. The surface's one context-dependent type is `=`.
//
// The two tests below are the bug's two faces, and they are separate on
// purpose: which one you get depends only on what the *preceding* field's
// type happens to be, so pinning one does not pin the other.

#[test]
fn a_parameter_at_a_dependent_type_keeps_its_scope() {
    // The loud face: with the parameter as the only field, a missing
    // weakening lands on the nominal tag's `⟨⟩`, which is not a `Nat`, so the
    // kernel rejects and nothing silently goes wrong.
    elab(
        "inductive Box<A> { Mk(A) }
         fn mk(n: Nat, p: n = n) -> Box<n = n> { Mk(p) }",
    );
}

#[test]
fn a_parameter_at_a_dependent_type_is_not_captured_by_an_earlier_field() {
    // The silent face, and the one that matters. With a `Nat` field before
    // it, a missing weakening lands on *that field* — same type, so the
    // encoding stays well-formed and `Box2<n = n>`'s second component quietly
    // becomes `x = x`. Nothing rejects; the declaration just means something
    // else. Only a test that can tell `n = n` from `3 = 3` sees it.
    elab(
        "inductive Box2<A> { Mk(x: Nat, y: A) }
         fn mk(n: Nat, p: n = n) -> Box2<n = n> { Mk(3, p) }",
    );
    let msg = elab_err(
        "inductive Box2<A> { Mk(x: Nat, y: A) }
         fn mk(n: Nat, q: 3 = 3) -> Box2<n = n> { Mk(3, q) }",
    );
    assert!(
        msg.contains("rejected"),
        "a proof of `3 = 3` was accepted where `n = n` was written: {msg}"
    );
    // …and the field really is `n = n`: projecting it back out proves it.
    elab(
        "inductive Box2<A> { Mk(x: Nat, y: A) }
         theorem out(n: Nat, p: n = n): n = n { match Mk(3, p) as z -> n = n { Mk(x, y) => y } }",
    );
}
