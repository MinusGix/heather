//! The equation binding and the `split` statement
//! (`docs/match-equation-split-design.md`).
//!
//! Two features, one node. `match h : e { … }` makes the elaborator write the
//! convoy — motive `λ z => (e = z) -> M z`, one `λ h` per arm, the whole thing
//! applied to `refl` — and `split e; on Ctor(x⃗) := b;` is a statement-position
//! spelling that the *parser* desugars onto the very same `ExprKind::Match`.
//! So neither adds an elimination form, and the suite's job is to show that:
//! the split path emits a term convertible with the `match` path's, and the
//! convoy path emits a term whose *type* is what the unconvoyed `match` would
//! have had.
//!
//! Per `docs/testing-generated-terms.md`: a **literal** scrutinee that must
//! compute and a **neutral** one (axis 1); an **open** payload type, a
//! declaration type parameter (axis 2); a **checking** position under a
//! dependent motive where the annotation must convert with a goal, not be
//! reduced away (axis 3); negative controls per decision (axis 4); and a
//! **three-constructor** inductive with an open payload throughout, so the
//! case tree's inner node is exercised at an ambient variable (axis 6).

use heather_elab::{ElabError, Elaborator};
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, LocalCtx, Term, Type};
use heather_kernel::typing::DEFAULT_FUEL;

/// Axis 6 + axis 2: three constructors, and the payload is a type parameter,
/// so every annotation inside the case tree mentions an ambient variable.
const PREAMBLE: &str = r#"
inductive Res<A> { Stuck, OutOfFuel, Out(v: A) }

fn once<A>(f: A -> Res<A>, r: Res<A>) -> Res<A> {
    match r {
        Stuck => Stuck,
        OutOfFuel => OutOfFuel,
        Out(v) => f(v),
    }
}

fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),
    }
}
"#;

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(PREAMBLE).unwrap_or_else(|err| panic!("preamble: {}", err.render(PREAMBLE)));
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn ok(src: &str) {
    elab(src);
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(PREAMBLE).expect("preamble");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated:\n{src}"),
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(ElabError::Parse(p)) => p.msg,
        Err(other) => format!("{other}"),
    }
}

/// The body of the last committed binding.
fn last_body(e: &Elaborator) -> Term {
    match e.psi().bindings.last().expect("a binding") {
        GlobalBinding::Tm { body: Some(b), .. } => (**b).clone(),
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

fn empty_ctx() -> LocalCtx {
    LocalCtx::nil()
}

// -- §5/§6: the `split` statement ------------------------------------------

/// The sketch's own example (`docs/sketches/surface-v1.md` §2), and axis 1's
/// literal half: the split-defined `add` must *compute*, not merely check.
#[test]
fn a_split_defines_a_recursive_function_and_it_computes() {
    // The `refl` is the assertion: the kernel has to *run* the elimination.
    ok(r#"
       fn add2(m: Nat, n: Nat) -> Nat {
           split m;
           on Zero := n;
           on Succ(k) := Succ(add2(k, n));
       }
       theorem add2_computes(): add2(2, 3) = 5 { refl }
       "#);
}

/// The equivalence control: `split` is a *spelling*, so the two bodies must be
/// the same elimination. Convertible at `Nat -> Nat -> Nat`, and — the vacuity
/// guard the codebase's equivalence tests carry — the two sources differ.
#[test]
fn a_split_emits_the_same_term_as_the_match() {
    let by_split = elab(
        "fn f(m: Nat, n: Nat) -> Nat { split m; on Zero := n; on Succ(k) := Succ(f(k, n)); }",
    );
    let by_match = elab(
        "fn f(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => Succ(f(k, n)) } }",
    );
    let (a, b) = (last_body(&by_split), last_body(&by_match));
    let ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: std::rc::Rc::new(Type::Nat),
        cod: std::rc::Rc::new(Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: std::rc::Rc::new(Type::Nat),
            cod: std::rc::Rc::new(Type::Nat),
        }),
    };
    conv_term(by_split.psi(), &empty_ctx(), Layer::Prog, &a, &b, &ty, &Level::Zero, DEFAULT_FUEL)
        .expect("split and match must build the same elimination");
    // …and they are literally the same term, which is the stronger claim the
    // parser desugaring earns (§6). Stated as an assertion so that a future
    // elaborator-side `split` would fail here rather than silently drift.
    assert_eq!(format!("{a:?}"), format!("{b:?}"));
}

/// Axis 2 + axis 6: a split over the three-constructor open-payload family,
/// so the arms sit under the case tree's inner `Inr` node with an ambient
/// type variable in every annotation.
#[test]
fn a_split_handles_three_constructors_at_an_open_payload() {
    ok(r#"
       fn get<A>(d: A, r: Res<A>) -> A {
           split r;
           on Stuck := d;
           on OutOfFuel := d;
           on Out(v) := v;
       }
       "#);
}

/// Axis 3: a split in a *checking* position — a `theorem`, where the motive is
/// synthesized from the goal and each arm's statement has to convert with it.
/// The self-call in the `Succ` arm is the induction hypothesis
/// (`issues/match-recursion.md`), reached through the `on` arm exactly as it
/// is through a `match` arm.
#[test]
fn a_split_proves_a_theorem_by_induction() {
    ok(r#"
       theorem add_zero(n: Nat): add(n, 0) = n {
           split n;
           on Zero := refl;
           on Succ(k) := cong_succ(add_zero(k));
       }
       "#);
}

/// A `split` and a goal discharge in one block: arms and `on ?g` share the
/// `on` loop and are told apart by one token, in either order (§5).
#[test]
fn a_split_coexists_with_a_goal_discharge() {
    ok(r#"
       theorem add_zero_g(n: Nat): add(n, 0) = n {
           split n;
           on Zero := refl;
           on Succ(k) := ?step;
           on ?step := cong_succ(add_zero_g(k));
       }
       "#);
    // …and the arms need not come first.
    ok(r#"
       theorem add_zero_g2(n: Nat): add(n, 0) = n {
           split n;
           on ?step := cong_succ(add_zero_g2(k));
           on Zero := refl;
           on Succ(k) := ?step;
       }
       "#);
}

/// §5.1: a split-terminated block *expression*. The `on Ctor` heads are arms,
/// consumed by the parser, so `Block::ons` is empty and
/// `docs/let-and-blocks-design.md` §4.3's refusal never fires.
#[test]
fn a_block_expression_may_split() {
    ok(r#"
       fn pred(m: Nat) -> Nat {
           { split m; on Zero := 0; on Succ(k) := k; }
       }
       theorem pred_computes(): pred(3) = 2 { refl }
       "#);
}

// -- §3: the equation binding ----------------------------------------------

/// The motivating shape, minimized from `lib/ir_v1.hthr`'s `step_mono`
/// `LoopIter` arm: a **neutral** scrutinee (`f1(a)`, which reduces to nothing),
/// an **open** payload, an explicit dependent motive, and a *checking*
/// position. The equation is load-bearing twice — `hyp(a, v, h)` transports the
/// goal, and `q` is the specialized hypothesis — and it is used **without a
/// `sym`**, which is §3.2's whole argument for the direction.
#[test]
fn the_equation_binding_carries_the_convoy() {
    ok(r#"
       theorem once_mono<A>(f1: A -> Res<A>, f2: A -> Res<A>,
                            hyp: (x: A) -> (w: A) -> f1(x) = Out(w) -> f2(x) = Out(w),
                            a: A, vs: A)
           : once(f1, f1(a)) = Out(vs) -> once(f2, f2(a)) = Out(vs)
       {
           match h : f1(a) as λ r =>
               once(f1, r) = Out(vs) -> once(f2, f2(a)) = Out(vs) {
               Stuck => λ q => absurd(q),
               OutOfFuel => λ q => absurd(q),
               Out(v) => λ q =>
                   j(sym(hyp(a, v, h)),
                     λ y p => once(f2, y) = Out(vs),
                     hyp(v, vs, q)),
           }
       }
       "#);
}

/// Axis 4, the negative control that makes the test above mean something: the
/// same proof **without** the binder is rejected, because nothing connects the
/// arm's `v` to `f1(a)`.
#[test]
fn without_the_equation_the_same_proof_fails() {
    let msg = bad(
        r#"
        theorem once_mono_bad<A>(f1: A -> Res<A>, f2: A -> Res<A>,
                                 hyp: (x: A) -> (w: A) -> f1(x) = Out(w) -> f2(x) = Out(w),
                                 a: A, vs: A)
            : once(f1, f1(a)) = Out(vs) -> once(f2, f2(a)) = Out(vs)
        {
            match f1(a) as λ r =>
                once(f1, r) = Out(vs) -> once(f2, f2(a)) = Out(vs) {
                Stuck => λ q => absurd(q),
                OutOfFuel => λ q => absurd(q),
                Out(v) => λ q => hyp(v, vs, q),
            }
        }
        "#,
    );
    assert!(!msg.is_empty(), "the unconvoyed proof must be rejected");
}

/// The equation is type-transparent (§3.3): with `motive: None` the whole
/// `match h : e { … }` still checks at the block's expected type, and the
/// result **computes** at a literal scrutinee — axis 1's other half, where a
/// wrong `Pi`/`App` annotation would be reduced away only if it were right.
#[test]
fn the_equation_binding_is_type_transparent_and_computes() {
    ok(r#"
       fn depth(r: Res<Nat>) -> Nat {
           match h : r {
               Stuck => 0,
               OutOfFuel => 0,
               Out(v) => Succ(v),
           }
       }
       theorem depth_computes(): depth(Out(3)) = 4 { refl }
       "#);
}

/// The binder really is in scope and really has the stated type — and the
/// *direction* is pinned here, not merely documented: `h` discharges an
/// `g(a) = Out(v)` obligation, and the flipped obligation is rejected. §3.2.
#[test]
fn the_binder_is_the_equation_scrutinee_equals_pattern() {
    const EQ_USED: &str = "fn eq_used<T>(x: T, y: T, p: x = y) -> Nat { 0 }\n";
    ok(&format!(
        "{EQ_USED}
         fn uses_h<A>(g: A -> Res<A>, a: A) -> Nat {{
             match h : g(a) {{
                 Stuck => 0,
                 OutOfFuel => 0,
                 Out(v) => eq_used(g(a), Out(v), h),
             }}
         }}"
    ));
    // The other direction needs a `sym`, which is exactly the tax the
    // hand-written convoy in `lib/ir_v1.hthr` was paying (§3.2).
    let msg = bad(&format!(
        "{EQ_USED}
         fn uses_h_flipped<A>(g: A -> Res<A>, a: A) -> Nat {{
             match h : g(a) {{
                 Stuck => 0,
                 OutOfFuel => 0,
                 Out(v) => eq_used(Out(v), g(a), h),
             }}
         }}"
    ));
    assert!(!msg.is_empty());
    ok(&format!(
        "{EQ_USED}
         fn uses_h_sym<A>(g: A -> Res<A>, a: A) -> Nat {{
             match h : g(a) {{
                 Stuck => 0,
                 OutOfFuel => 0,
                 Out(v) => eq_used(Out(v), g(a), sym(h)),
             }}
         }}"
    ));
}

/// On `Nat`, and through a `split` (§7): the same field, so the same convoy.
#[test]
fn a_split_takes_the_equation_binder() {
    ok(r#"
       fn is_zero(m: Nat) -> Nat {
           split h : add(m, 0);
           on Zero := 1;
           on Succ(k) := 0;
       }
       theorem is_zero_computes(): is_zero(0) = 1 { refl }
       "#);
}

// -- §4: the indexed-family refusal ----------------------------------------

/// §4.1: not a deferral. On an indexed family an arm's index varies with its
/// constructor, so `e = pat` would relate two values at different types, and
/// homogeneous `Id` cannot say that. The message names the family and points
/// at the inversion-lemma route.
#[test]
fn the_equation_binding_is_refused_on_an_indexed_family() {
    let msg = bad(
        r#"
        inductive MN { MZ, MS(p: MN) }
        inductive VF<A> : (n: MN) -> Type {
            VFNil                            : VF<A>(MZ),
            VFCons(n: MN, x: A, xs: VF<A>(n)) : VF<A>(MS(n)),
        }

        fn lenf(n: MN, xs: VF<Nat>(n)) -> MN {
            match h : xs {
                VFNil => MZ,
                VFCons(k, x, t) => k,
            }
        }
        "#,
    );
    assert!(
        msg.contains("indexed family") && msg.contains("inversion"),
        "expected the §4 message, got: {msg}"
    );
}

// -- axis 4: the parser's negative controls --------------------------------

#[test]
fn an_on_arm_needs_a_split() {
    let msg = bad("fn f(m: Nat) -> Nat { m on Zero := 0; }");
    assert!(msg.contains("has no `split`"), "got: {msg}");
}

#[test]
fn a_split_is_the_last_statement() {
    let msg = bad("fn f(m: Nat) -> Nat { split m; let x = 1; on Zero := 0; on Succ(k) := k; }");
    assert!(msg.contains("last statement"), "got: {msg}");
}

#[test]
fn a_split_needs_an_arm() {
    let msg = bad("fn f(m: Nat) -> Nat { split m; }");
    assert!(msg.contains("at least one"), "got: {msg}");
}

#[test]
fn split_is_not_a_binding_name() {
    let msg = bad("fn f(n: Nat) -> Nat { let split = n; split }");
    assert!(msg.contains("case-split statement keyword"), "got: {msg}");
}

/// The elaborator's existing arm checks are the split's error behaviour (§8):
/// they cost nothing because the desugaring hands them the same `Arm`s a
/// `match` would.
#[test]
fn a_splits_arms_are_checked_like_a_matchs() {
    assert!(bad("fn f(m: Nat) -> Nat { split m; on Foo := 0; on Succ(k) := k; }")
        .contains("not a constructor"));
    assert!(bad("fn f(m: Nat) -> Nat { split m; on Zero := 0; }").contains("Succ"));
    assert!(bad("fn f(m: Nat) -> Nat { split m; on Zero := 0; on Zero := 1; }")
        .contains("duplicate arm"));
    assert!(bad(
        "fn f<A>(d: A, r: Res<A>) -> A {
             split r; on Stuck := d; on OutOfFuel := d; on Out(v, w) := v; }"
    )
    .contains("field"));
}

/// A `split` on something with no constructors at all.
#[test]
fn a_split_needs_an_inductive() {
    let msg = bad("fn f(g: Nat -> Nat) -> Nat { split g; on Zero := 0; on Succ(k) := k; }");
    assert!(msg.contains("declared inductive"), "got: {msg}");
}

/// The convoy is a `Pi` around a motive, and every lowering takes the motive
/// as an opaque `Type` (§1.1(a)) — so the feature reaches all of them, not just
/// the tier-0 case tree the tests above exercise. One each: **tier 1** (a
/// recursive inductive, `elab_match_wf`), `Empty` (zero arms, vacuous but well
/// typed), and `Fin`, which is *not* refused by §4 because its motive binds one
/// thing at a fixed length and the equation stays homogeneous.
#[test]
fn the_convoy_reaches_every_lowering() {
    ok(r#"
       inductive Tr<A> { Leaf, Node(l: Tr<A>, v: A, r: Tr<A>) }
       fn idt<A>(t: Tr<A>) -> Tr<A> { t }
       theorem idt_id<A>(t: Tr<A>): idt(t) = t {
           match h : t as λ z => idt(z) = z { Leaf => refl, Node(l, v, r) => refl }
       }
       "#);
    ok("inductive Void { }\nfn f(x: Void) -> Nat { match h : x { } }");
    ok("fn f(k: Nat, i: Fin(Succ(k))) -> Nat { match h : i { FZ => 0, FS(jx) => 1 } }");
}

// -- §6's stated cost, paid (issues/diagnostics-name-the-written-form.md) ---

/// §6 shipped with a wart written down: the desugaring's messages say
/// `match` at a block whose text says `split`. Every message that names a
/// form now asks the node which spelling built it.
///
/// Seven sites, not the five §6 estimated — the count is the *naming* sites,
/// and three of the five it listed (unknown constructor, duplicate arm, wrong
/// arity) never named a form at all, while `Fin`, the empty type and the
/// motive refusal do.
#[test]
fn a_splits_diagnostics_name_split() {
    let m = bad("fn f<A>(d: A, r: Res<A>) -> A { split r; on Stuck := d; on OutOfFuel := d; }");
    assert!(m.contains("`split` is missing an arm for `Out`"), "got: {m}");

    let m = bad("fn f(g: Nat -> Nat) -> Nat { split g; on Zero := 0; on Succ(k) := k; }");
    assert!(m.contains("`split` needs a `Nat` or a declared inductive"), "got: {m}");

    let m = bad("fn f(m: Nat) -> Nat { split m; on Zero := 0; }");
    assert!(m.contains("`split` on `Nat` needs both"), "got: {m}");

    let m = bad("fn f(k: Nat, i: Fin(Succ(k))) -> Nat { split i; on FZ := 0; }");
    assert!(m.contains("`split` on a `Fin` needs both an `FZ`"), "got: {m}");

    let m = bad("inductive Void { }\nfn f(x: Void) -> Nat { split x; on Zero := 0; }");
    assert!(m.contains("so `split` takes no arms"), "got: {m}");

    // Not just the form's name: the *spelling it suggests* is one a writer
    // who typed `split` can paste. `match e as λ z => T { … }` is not.
    let m = bad(
        "fn f<A>(d: A, r: Res<A>) -> A {
             let x = { split r; on Stuck := d; on OutOfFuel := d; on Out(v) := v; }; x }",
    );
    assert!(m.contains("`split` in inference position"), "got: {m}");
    assert!(m.contains("`split e as \u{3bb} z => T;`"), "got: {m}");

    // The one place a `match` still appears inside a `split`'s message, and
    // deliberately: the suggestion is a *new* elimination on the length, not
    // a respelling of the one that failed.
    let m = bad("fn f(n: Nat, i: Fin(n)) -> Nat { split i; on FZ := 0; on FS(j) := 1; }");
    assert!(m.contains("`split` on a `Fin` needs its length to reduce"), "got: {m}");
    assert!(m.contains("Recurse on the length first"), "got: {m}");
}

/// The control the test above needs: a written `match` still says `match` at
/// all seven. Without it, hard-coding `split` everywhere would pass.
#[test]
fn a_matchs_diagnostics_still_name_match() {
    let m = bad("fn f<A>(d: A, r: Res<A>) -> A { match r { Stuck => d, OutOfFuel => d } }");
    assert!(m.contains("`match` is missing an arm for `Out`"), "got: {m}");

    let m = bad("fn f(g: Nat -> Nat) -> Nat { match g { Zero => 0, Succ(k) => k } }");
    assert!(m.contains("`match` needs a `Nat` or a declared inductive"), "got: {m}");

    let m = bad("fn f(m: Nat) -> Nat { match m { Zero => 0 } }");
    assert!(m.contains("`match` on `Nat` needs both"), "got: {m}");

    let m = bad("fn f(k: Nat, i: Fin(Succ(k))) -> Nat { match i { FZ => 0 } }");
    assert!(m.contains("`match` on a `Fin` needs both an `FZ`"), "got: {m}");

    let m = bad("inductive Void { }\nfn f(x: Void) -> Nat { match x { Zero => 0 } }");
    assert!(m.contains("so `match` takes no arms"), "got: {m}");

    let m = bad(
        "fn f<A>(d: A, r: Res<A>) -> A {
             let x = match r { Stuck => d, OutOfFuel => d, Out(v) => v }; x }",
    );
    assert!(m.contains("`match` in inference position"), "got: {m}");
    assert!(m.contains("`match e as \u{3bb} z => T { … }`"), "got: {m}");

    let m = bad("fn f(n: Nat, i: Fin(n)) -> Nat { match i { FZ => 0, FS(j) => 1 } }");
    assert!(m.contains("`match` on a `Fin` needs its length to reduce"), "got: {m}");
}

/// The pattern compiler's own three, which the seven above missed.
///
/// The round that threaded `MatchForm` recorded the inherited form on a
/// *generated* inner level as "honest but unobservable, because a `split`
/// arm's binders are plain names". That premise is wrong: a `split` arm's
/// binders come from the same `pat_args` a `match` arm's do
/// (`crates/syntax/src/parser.rs`), so a deep pattern is writable in an `on`
/// arm, and the inheritance is observable — the first case below is the
/// generated level naming the form nobody wrote at.
#[test]
fn a_splits_deep_patterns_name_split() {
    // The generated inner level, which has no source text of its own and so
    // can only inherit. (Its *span* is still the outer `split` — that is
    // issues/diagnostics-name-the-written-form.md item 2, unpaid.)
    let m = bad(
        "fn f<A>(d: A, r: Res<Res<A>>) -> A {
             split r; on Stuck := d; on OutOfFuel := d; on Out(Out(v)) := v; }",
    );
    // Named in full: the outer column is exhaustive (all three arms are
    // there), so only the generated inner level can be missing these two.
    assert!(m.contains("`split` is missing an arm for `Stuck`, `OutOfFuel`"), "got: {m}");

    // §6: a deep pattern under the termination guard.
    let m = bad(
        "fn f<A>(d: A, r: Res<Res<A>>) -> A {
             split r; on Stuck := d; on OutOfFuel := d; on Out(Out(v)) := f(d, r); }",
    );
    assert!(m.contains("a deep pattern is not available in this `split`"), "got: {m}");
    // The advice it gives is a nested `match` inside the arm, and stays one:
    // a fresh elimination in the arm body is a spelling either form can hold.
    assert!(m.contains("nested `match` inside the arm"), "got: {m}");

    // A constructor at two arities in one column.
    let m = bad(
        "fn f<A>(d: A, r: Res<Res<A>>) -> A {
             split r; on Stuck := d; on OutOfFuel := d;
             on Out(Out(v)) := v; on Out(Out()) := d; }",
    );
    assert!(m.contains("in an earlier pattern of this `split`"), "got: {m}");
}

/// The control for the three above.
#[test]
fn a_matchs_deep_patterns_still_name_match() {
    let m = bad(
        "fn f<A>(d: A, r: Res<Res<A>>) -> A {
             match r { Stuck => d, OutOfFuel => d, Out(Out(v)) => v } }",
    );
    assert!(m.contains("`match` is missing an arm for `Stuck`, `OutOfFuel`"), "got: {m}");

    let m = bad(
        "fn f<A>(d: A, r: Res<Res<A>>) -> A {
             match r { Stuck => d, OutOfFuel => d, Out(Out(v)) => f(d, r) } }",
    );
    assert!(m.contains("a deep pattern is not available in this `match`"), "got: {m}");

    let m = bad(
        "fn f<A>(d: A, r: Res<Res<A>>) -> A {
             match r { Stuck => d, OutOfFuel => d, Out(Out(v)) => v, Out(Out()) => d } }",
    );
    assert!(m.contains("in an earlier pattern of this `match`"), "got: {m}");
}

/// The advice the motive message now gives is followable — which is the
/// point of changing it, and the half a message-text assertion cannot show.
#[test]
fn the_suggested_split_motive_spelling_checks() {
    ok(r#"
       fn f<A>(d: A, r: Res<A>) -> A {
           let x = {
               split r as λ z => A;
               on Stuck := d;
               on OutOfFuel := d;
               on Out(v) := v;
           };
           x
       }
       "#);
}
