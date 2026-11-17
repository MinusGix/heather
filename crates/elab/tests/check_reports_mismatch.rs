//! Checking that ends in inference reports the mismatch itself
//! (`issues/check-fallback-discards-expected-type.md`).
//!
//! The simplest type error in the language used to be a bare kernel
//! `NotConvertible` at the whole declaration: the fallback held an inferred type
//! and dropped it. The claim tested here is narrow and it is *not* "the
//! elaborator typechecks". The mismatch is *recorded* during checking and read
//! only by the kernel gate, only when the gate itself rejects — so nothing is
//! reported that the kernel did not refuse, and a more specific diagnostic
//! raised further down the same declaration still wins the message. The
//! controls pin that boundary: a phantom argument the display will not guess,
//! a type that converts only after δ and β, a `refl` whose sides likewise meet
//! only after δ and β, a projection that converts only through a `fn`, and a
//! kernel refusal of another class, which keeps the kernel's own report.
//!
//! A mismatch the conversion decides but the display cannot state keeps the
//! gate's report and moves it to the expression, the way a `refl` note does
//! (`issues/elab-accepts-projection-through-opaque-theorem.md`).
//!
//! `refl` joined the same mechanism in
//! `issues/elab-refl-accepts-match-eta-kernel-rejects.md`, one step short of
//! it: it is the checking form that compares *nothing*, so a false equation
//! was the last bare `NotConvertible` at a declaration. Its note does not
//! replace the gate's report — the certifying pipeline's mutation controls
//! read that verdict, and their `refl` pins have sides no display can spell —
//! it moves the report to the `refl` and appends the two sides.

use heather_elab::{ElabError, Elaborator, KernelSite};
use heather_kernel::typing::TypeError;

const LIST: &str = "
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
fn append<A>(xs: List<A>, ys: List<A>) -> List<A> {
    match xs { Nil => ys, Cons(h, t) => Cons(h, append(t, ys)) }
}
";

fn reject(src: &str) -> ElabError {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err,
    }
}

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

/// The filed acceptance case. A numeral is the leaf where the inferred type is
/// free, so this is the cheap half of the fix.
#[test]
fn a_literal_at_the_wrong_type_reports_at_the_literal() {
    let src = format!("{LIST}fn d5<A>(xs: List<A>) -> List<A> {{ 3 }}\n");
    let r = reject(&src);
    let rendered = r.render(&src);
    assert!(
        rendered.contains("this has type `Nat`, but `List<A>` is expected here"),
        "{rendered}"
    );
    assert!(!rendered.contains("the kernel rejected"), "{rendered}");
    // At the `3`, not at the declaration.
    let ElabError::Elab { span, .. } = r else { panic!("expected an elaborator error: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "3");
}

/// A variable at the wrong type takes the general route — the `_` arm of
/// `elab_check_skel` — rather than the numeral's.
#[test]
fn a_variable_at_the_wrong_type_reports_at_the_variable() {
    let src = format!("{LIST}fn d6<A>(xs: List<A>, n: Nat) -> List<A> {{ n }}\n");
    let r = reject(&src);
    let rendered = r.render(&src);
    assert!(
        rendered.contains("this has type `Nat`, but `List<A>` is expected here"),
        "{rendered}"
    );
    let ElabError::Elab { span, .. } = r else { panic!("expected an elaborator error: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "n");
}

/// A *call* at the wrong type — not a leaf, so its inferred type is a computed
/// instantiation. The round measured whether to cover this: the conversion at
/// every checked expression moves the frontend suite by less than its own
/// run-to-run noise, so the coverage is free and the narrow variants the issue
/// proposed were not worth their narrowing.
#[test]
fn a_call_at_the_wrong_type_reports_at_the_call() {
    let src = format!("{LIST}fn d7<A>(xs: List<A>) -> Nat {{ append(xs, xs) }}\n");
    let rendered = reject(&src).render(&src);
    assert!(
        rendered.contains("this has type `List<A>`, but `Nat` is expected here"),
        "{rendered}"
    );
    assert!(!rendered.contains("the kernel rejected"), "{rendered}");
}

/// Type arguments recovered from distinct payload positions make this
/// mismatch stateable. Re-lowering verifies the candidates before the display
/// path is allowed to make the claim.
#[test]
fn a_mismatch_between_inductive_instantiations_is_stated() {
    let src = "
inductive And<A, B> { Both(left: A, right: B) }
theorem t(p: And<True, True>, q: And<True, And<True, True>>): True {
    match p { Both(l, r) => l }
}
fn wrong(p: And<True, And<True, True>>) -> And<True, True> { p }
";
    let rendered = reject(src).render(src);
    assert!(
        rendered.contains(
            "this has type `And<True, And<True, True>>`, but `And<True, True>` is expected here"
        ),
        "{rendered}"
    );
    assert!(!rendered.contains("the kernel rejected"), "{rendered}");
}

/// A phantom parameter has no structural witness in the lowering. (Indeed,
/// two phantom instantiations are definitionally the same kernel type.) An
/// unrelated mismatch therefore keeps the honest ellipsis rather than
/// inventing a type argument.
#[test]
fn a_phantom_inductive_argument_is_not_guessed() {
    let src = "
inductive Phantom<A> { Mark }
fn wrong() -> Phantom<Nat> { 0 }
";
    let rendered = reject(src).render(src);
    assert!(
        rendered.contains("this has type `Nat`, but `Phantom<…>` is expected here"),
        "{rendered}"
    );
    assert!(!rendered.contains("Phantom<Nat>"), "{rendered}");
}

/// A false equation under `refl`
/// (`issues/elab-refl-accepts-match-eta-kernel-rejects.md`). `refl` is a
/// checking form that emits `Refl(lhs)` and compares nothing, so the verdict
/// is the gate's and stays spelled as the gate's — what the note adds is the
/// span of the `refl` that claimed the conversion, and the two sides.
#[test]
fn a_false_equation_reports_at_the_refl() {
    let src = "theorem broken(n: Nat): n = Succ(n) { refl }\n";
    let r = reject(src);
    let rendered = r.render(src);
    assert!(rendered.contains("the kernel rejected `broken`: NotConvertible"), "{rendered}");
    assert!(
        rendered.contains(
            "`refl` needs both sides to be definitionally equal, \
             but `n` and `Succ(n)` are not"
        ),
        "{rendered}"
    );
    // At the `refl`, not at the declaration.
    let ElabError::Kernel { span, .. } = r else { panic!("expected a kernel rejection: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "refl");
}

/// The shape the issue was filed on: a `match` on a **neutral** scrutinee
/// whose arms each rebuild the constructor they matched. Neither the kernel
/// nor the elaborator has a match-eta, so this is refused — the round's claim
/// is only that the refusal says which two sides failed to meet, at the
/// `refl`. (`int::Int::add(x, OfNat(0)) = x` is this, one library away.)
#[test]
fn a_match_eta_names_both_sides() {
    let src = "
inductive Two { L(n: Nat), R(n: Nat) }
fn id2(a: Two) -> Two { match a { L(m) => L(m), R(m) => R(m) } }
theorem eta(a: Two): id2(a) = a { refl }
";
    let rendered = reject(src).render(src);
    assert!(
        rendered.contains(
            "`refl` needs both sides to be definitionally equal, \
             but `id2(a)` and `a` are not"
        ),
        "{rendered}"
    );
}

/// **Negative control, and the architectural one.** The note is a report, not
/// a check: a `refl` whose sides meet only after δ and β is still accepted,
/// and nothing about the equation is decided before the kernel sees it.
#[test]
fn a_refl_that_only_converts_is_still_accepted() {
    ok("
        fn dbl(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(dbl(k))) } }
        theorem four(): dbl(2) = 4 { refl }
        ");
}

/// **Negative control, the architectural one at the other end.** The
/// elaborator does not become the judge: a kernel refusal it holds no note
/// about keeps the kernel's own report, class and all.
#[test]
fn the_kernel_is_still_the_judge() {
    // A `meta fn` whose body has the wrong type: the meta gate maps the
    // kernel's verdict straight through, with no note
    // (issues/meta-fn-mismatch-reaches-kernel.md), so the gate's own report
    // stands, class and all. When that issue closes, this needs another
    // kernel-only refusal.
    let src = "
meta fn s(g: Ctx, n: Nat) -> Code(g |- Nat) { n }
";
    let r = reject(src);
    let rendered = r.render(src);
    assert!(rendered.contains("the kernel rejected `s`: NotConvertible"), "{rendered}");
    // No note, so the span stays where the gate put it: the declaration.
    let ElabError::Kernel { span, .. } = r else { panic!("expected a kernel rejection: {r}") };
    assert!(src[span.start as usize..span.end as usize].starts_with("meta fn s("), "{rendered}");
}

/// **Negative control, the one that would break real programs.** The comparison
/// is a *conversion*, not an equality of representations: an expected type that
/// is a lazily wrapped code (`El(Alias())`, δ- and β-steps away from `Nat`) must
/// still accept a `Nat`. This is the open/lazy-type axis of
/// `docs/testing-generated-terms.md`, and a syntactic check would fail it.
#[test]
fn a_type_that_only_converts_is_still_accepted() {
    ok("
        fn Alias() -> Type { Nat }
        fn k(n: Nat) -> Alias() { n }
        fn uses(n: Nat) -> Nat { k(n) }
        ");
}

/// The note is **deferred to the verdict**, and the verdict is reported from
/// the serial path at every width (`issues/elab-diagnostic-probe-cost.md`).
///
/// The candidate is recorded while the body walks and its conversion runs only
/// if the gate rejects — so the one thing that could have been lost is the
/// thing the note exists for: a span *inside* the body, which the
/// declaration-level failure cannot name. Both notes are checked, at the
/// inline width and at a real pool: under the parallel gate the join reports
/// no note at all, the pass is discarded and replayed serially, and it is the
/// replay's `kernel_error` that must produce the same message at the same
/// span (`docs/kernel/parallel-kernel-gate-design.md` §5.1).
#[test]
fn a_deferred_note_survives_every_gate_width() {
    let mismatch = format!("{LIST}fn d_w<A>(xs: List<A>, n: Nat) -> List<A> {{ n }}\n");
    let refl = "
fn dbl(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(dbl(k))) } }
theorem three(): dbl(1) = 3 { refl }
";
    for workers in [1usize, 4] {
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.set_kernel_workers(workers);
        let err = match e.elab_module_source("w", &mismatch) {
            Ok(()) => panic!("expected a rejection at {workers} workers"),
            Err(err) => err,
        };
        let rendered = err.render(&mismatch);
        assert!(
            rendered.contains("this has type `Nat`, but `List<A>` is expected here"),
            "at {workers} workers: {rendered}"
        );
        let ElabError::Elab { span, .. } = err else {
            panic!("expected an elaborator error at {workers} workers: {err}")
        };
        assert_eq!(&mismatch[span.start as usize..span.end as usize], "n");

        let mut e = Elaborator::with_prelude().expect("prelude");
        e.set_kernel_workers(workers);
        let err = match e.elab_module_source("r", refl) {
            Ok(()) => panic!("expected a rejection at {workers} workers"),
            Err(err) => err,
        };
        let rendered = err.render(refl);
        assert!(
            rendered.contains("`refl` needs both sides to be definitionally equal"),
            "at {workers} workers: {rendered}"
        );
        // The verdict stays the kernel's; only the span moves to the `refl`.
        let ElabError::Kernel { span, .. } = err else {
            panic!("expected a kernel rejection at {workers} workers: {err}")
        };
        assert_eq!(&refl[span.start as usize..span.end as usize], "refl");
    }
}

const WITNESS: &str = "
record W { after: Nat, pres: after = 0 }
";

/// A field projection in checking position synthesizes, and was the one
/// synthesizing arm that returned without recording what it synthesized
/// (`issues/elab-accepts-projection-through-opaque-theorem.md`). An axiom is
/// opaque, so `mk_w().after` is stuck and `mk_w().pres` does not prove `0 = 0`;
/// the gate's refusal used to land on the declaration with nothing named.
/// (This was a `theorem` until a theorem whose statement carries data kept
/// its proof sealed and a projection opened it,
/// `issues/theorem-witness-unfolding.md`: `mk_w().after` now computes to
/// `0` through one, and the axiom is what is still stuck.)
#[test]
fn a_projection_at_the_wrong_type_reports_at_the_projection() {
    for body in ["mk_w().pres", "let w = mk_w(); w.pres"] {
        let src = format!(
            "{WITNESS}axiom mk_w(): W;\n\
             theorem t(): 0 = 0 {{ {body} }}\n"
        );
        let r = reject(&src);
        let rendered = r.render(&src);
        assert!(
            rendered.contains("but `0 = 0` is expected here"),
            "{body}: {rendered}"
        );
        // Why `mk_w().after` is not `0`: nothing will ever compute it
        // (`issues/stuck-on-opaque-theorem-diagnostic.md`).
        assert!(
            rendered.contains("`mk_w` is an axiom, so it has no proof to unfold"),
            "{body}: {rendered}"
        );
        let ElabError::Elab { span, .. } = r else { panic!("expected an elaborator error: {r}") };
        assert!(src[span.start as usize..span.end as usize].ends_with(".pres"), "{rendered}");
    }
}

/// **Control for the projection note.** The same projection through a `fn`,
/// which unfolds, converts and is accepted: the note is a record, and only
/// the gate's refusal reads it. Through a `theorem` it is accepted too: `W`
/// carries data, so the projection opens the theorem's sealed proof.
#[test]
fn a_projection_that_converts_is_still_accepted() {
    for head in ["fn mk_w() -> W", "theorem mk_w(): W"] {
        ok(&format!(
            "{WITNESS}{head} {{ W(after := 0, pres := refl) }}\n\
             theorem t(): 0 = 0 {{ mk_w().pres }}\n"
        ));
    }
}

/// A mismatch the conversion decides but the display cannot state: the
/// hypothesis is spelled per arm (`match r { … => dbl(p) … }`), the goal
/// outside the match (`dbl(payload(r))`), and the kernel has no commuting
/// conversion between the two. `Step` is recursive (`More`), so the display
/// does not resugar the case analysis over it as a `match`. Neither the
/// claim nor silence: the verdict stays the gate's, its span moves to the
/// expression, and the note shows the side that spells (the second instance
/// in `issues/elab-accepts-projection-through-opaque-theorem.md`).
#[test]
fn an_unspellable_mismatch_moves_the_kernel_report_to_the_site() {
    let src = "
inductive Step { Go(next: Nat), Stop(result: Nat), More(rest: Step) }
fn payload(s: Step) -> Nat { match s { Go(p) => p, Stop(p) => p, More(t) => payload(t) } }
fn dbl(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(dbl(k))) } }
theorem t(r: Step, w: Nat, h: w = match r { Go(p) => dbl(p), Stop(p) => dbl(p), More(t) => dbl(payload(t)) }): w = dbl(payload(r)) {
    h
}
";
    let r = reject(src);
    let rendered = r.render(src);
    assert!(rendered.contains("the kernel rejected `t`: NotConvertible"), "{rendered}");
    assert!(
        rendered.contains("does not convert to `w = dbl(payload(r))`"),
        "{rendered}"
    );
    let ElabError::Kernel { span, .. } = r else { panic!("expected a kernel rejection: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "h");
}

/// The same mismatch over a non-recursive `Step` now spells: the case
/// analysis prints as the `match` it came from, so the elaborator states the
/// mismatch at `h` itself (`issues/induct-case-goal-report.md` item 3).
#[test]
fn a_match_over_fielded_constructors_spells_the_mismatch() {
    let src = "
inductive Step { Go(next: Nat), Stop(result: Nat) }
fn payload(s: Step) -> Nat { match s { Go(p) => p, Stop(p) => p } }
fn dbl(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(dbl(k))) } }
theorem t(r: Step, w: Nat, h: w = match r { Go(p) => dbl(p), Stop(p) => dbl(p) }): w = dbl(payload(r)) {
    h
}
";
    let r = reject(src);
    let rendered = r.render(src);
    assert!(
        rendered.contains("`w = match r { Go(next) => dbl(next), Stop(result) => dbl(result) }`"),
        "{rendered}"
    );
    assert!(rendered.contains("but `w = dbl(payload(r))` is expected here"), "{rendered}");
    let ElabError::Elab { span, .. } = r else { panic!("expected an elaborator error: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "h");
}

/// `lib/std/core/logic.hthr`'s `Exists`, which `∃` spells.
const EXISTS: &str = "record Exists<A>(P: A → Type) { witness: A, proof: P(witness) }\n";

/// A `refl` refused because the reduction it needed is stuck on a global that
/// never unfolds (`issues/stuck-on-opaque-theorem-diagnostic.md`). Read alone,
/// "`ex().witness` and `3` are not" says the number is wrong; the note says
/// instead that nothing will ever compute `ex().witness`, and why.
#[test]
fn a_refl_stuck_on_an_axiom_names_the_axiom() {
    let src = format!(
        "{EXISTS}axiom ex(k: Nat): ∃ n: Nat, n = 3;\n\
         theorem t(): ex(0).witness = 3 {{ refl }}\n"
    );
    let r = reject(&src);
    let rendered = r.render(&src);
    assert!(
        rendered.contains("but `ex(0).witness` and `3` are not"),
        "{rendered}"
    );
    assert!(
        rendered.contains("`ex` is an axiom, so it has no proof to unfold"),
        "{rendered}"
    );
    let ElabError::Kernel { span, .. } = r else { panic!("expected a kernel rejection: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "refl");
}

/// The theorem half of the same note: a theorem whose statement the sealing
/// test does not judge to carry data keeps no proof (`sealing.rs`). A
/// statement that decodes through a `match` on a parameter is such a
/// statement — a family the test reads as propositions — even when every arm
/// is an `∃`. A theorem whose statement does carry data is opened by the
/// projection and needs no note (`a_projection_that_converts_is_still_accepted`).
#[test]
fn a_refl_stuck_on_an_unkept_theorem_names_the_theorem() {
    let src = format!(
        "{EXISTS}fn Pick(k: Nat) -> Type {{ match k {{ Zero => ∃ n: Nat, n = 3, Succ(j) => ∃ n: Nat, n = 3 }} }}\n\
         theorem ex(k: Nat): Pick(k) {{ match k {{ Zero => Exists(3, refl), Succ(j) => Exists(3, refl) }} }}\n\
         theorem t(): ex(0).witness = 3 {{ refl }}\n"
    );
    let rendered = reject(&src).render(&src);
    assert!(
        rendered.contains("`ex` is a theorem whose statement was not judged to carry data"),
        "{rendered}"
    );
    assert!(rendered.contains("declare it as a `fn`"), "{rendered}");
}

/// **Control for the opaque-head note.** The same projection through a `fn`
/// unfolds and is accepted; through a `fn` with a false equation the `refl`
/// note stays, but nothing is stuck on an opaque global, so nothing is named.
#[test]
fn a_refl_through_a_fn_is_accepted_and_names_no_opaque_global() {
    ok(&format!(
        "{EXISTS}fn ex() -> ∃ n: Nat, n = 3 {{ Exists(3, refl) }}\n\
         theorem t(): ex().witness = 3 {{ refl }}\n"
    ));
    let src = format!(
        "{EXISTS}fn ex() -> ∃ n: Nat, n = 3 {{ Exists(3, refl) }}\n\
         theorem t(): ex().witness = 4 {{ refl }}\n"
    );
    let rendered = reject(&src).render(&src);
    assert!(rendered.contains("`refl` needs both sides to be definitionally equal"), "{rendered}");
    assert!(!rendered.contains("never unfolds") && !rendered.contains("axiom"), "{rendered}");
}

/// Callees for the inferred-argument cases: `a` is implicit and appears in
/// the explicit parameter's type, at a closed `Nat` (`f`), as a curried
/// parameter after the implicit telescope (`k`), at an open element type
/// (`g`), and in a value-parameterised constructor's field (`Q`).
const OWED: &str = "
theorem f({a: Nat}, h: 0 = a): a = a { refl }
theorem k({a: Nat}): (0 = a) -> a = a { λ h => refl }
theorem g<A>({a: A}, z: A, h: z = a): a = a { refl }
theorem same(x: Nat): x = x { refl }
inductive Q(n: Nat) { MkQ(e: 0 = n) }
";

/// An inferred argument whose parameter type mentions an implicit
/// (`issues/implicit-argument-mismatch-reaches-kernel.md`). Its type only
/// *teaches* the call's implicits, and that unification is learn-only, so
/// `h: a = a` at `0 = ?a` was compared with its parameter by nobody before
/// the kernel, which refused the declaration as a bare `NotConvertible`.
/// Now the call owes that comparison and records it at its discharge. Each
/// case was the kernel's refusal before: whether the expected type or the
/// argument itself solves `a` (`let`, no expected type), whether the
/// argument is a variable or a call, a curried parameter, an `@` call, a
/// receiver, a named argument, a constructor field, and an open type.
#[test]
fn an_inferred_argument_at_an_implicit_bearing_parameter_reports_at_the_argument() {
    let cases = [
        ("theorem bad(a: Nat, h: a = a): a = a { f(h) }", "h", "`a = a`, but `0 = a`"),
        ("theorem bad(a: Nat): a = a { f(same(a)) }", "same(a)", "`a = a`, but `0 = a`"),
        ("theorem bad(a: Nat, h: a = a): a = a { let r = f(h); r }", "h", "`a = a`, but `0 = a`"),
        ("theorem bad(a: Nat, h: a = a): a = a { k(h) }", "h", "`a = a`, but `0 = a`"),
        ("theorem bad(a: Nat, h: a = a): a = a { @f(a, h) }", "h", "`a = a`, but `0 = a`"),
        ("theorem bad(a: Nat, h: a = a): a = a { h.f() }", "h", "`a = a`, but `0 = a`"),
        ("theorem bad(a: Nat, h: a = a): a = a { f(h := h) }", "h", "`a = a`, but `0 = a`"),
        ("theorem bad(a: Nat, h: a = a): Q(a) { let q = Q::MkQ(h); q }", "h", "`a = a`, but `0 = a`"),
        ("theorem bad<A>(x, y: A, h: x = x): x = x { g(y, h) }", "h", "`x = x`, but `y = x`"),
    ];
    for (case, at, types) in cases {
        let src = format!("{OWED}{case}\n");
        let r = reject(&src);
        let rendered = r.render(&src);
        assert!(rendered.contains(&format!("this has type {types} is expected here")), "{case}\n{rendered}");
        assert!(!rendered.contains("the kernel rejected"), "{case}\n{rendered}");
        let ElabError::Elab { span, .. } = r else { panic!("{case}: expected an elaborator error: {r}") };
        let start = src.rfind(case).unwrap() + case.find('{').unwrap();
        assert!(span.start as usize > start, "{case}: reported outside the body\n{rendered}");
        assert_eq!(&src[span.start as usize..span.end as usize], at, "{case}\n{rendered}");
    }
}

/// **Control for the owed comparison.** The same calls with arguments of the
/// right type are accepted: the note is recorded, never probed, on a
/// declaration the gate accepts.
#[test]
fn an_inferred_argument_of_the_right_type_is_accepted() {
    ok(&format!(
        "{OWED}theorem good(a: Nat, h: 0 = a): a = a {{ f(h) }}\n\
         theorem good_let(a: Nat, h: 0 = a): a = a {{ let r = f(h); r }}\n\
         theorem good_curried(a: Nat, h: 0 = a): a = a {{ k(h) }}\n\
         theorem good_field(a: Nat, h: 0 = a): Q(a) {{ let q = Q::MkQ(h); q }}\n\
         theorem good_open<A>(x, y: A, h: y = x): x = x {{ g(y, h) }}\n"
    ));
}

const REDEX: &str = "
record And<P, Q> { left: P, right: Q }
theorem weaken_like(pre, entry: Nat → Type, into: (s: Nat) → entry(s) → pre(s)): True { trivial }
";

/// A mismatch whose type has a β-redex in it
/// (`issues/elab-accepts-mismatch-under-redex-head.md`). A `let`-bound λ at
/// the head of an annotation, or a binder whose type is an instantiated λ
/// parameter (`entry(s)` with `entry := λ s => P(s)`), leaves a redex in the
/// type the note holds. The note was recorded and the gate refused at the
/// right expression, but a redex has no surface spelling, so the report was
/// the kernel's `NotConvertible` with one side unspelled. The display now
/// spells a redex as its contractum, at the head and inside an argument, and
/// through a curried spine.
#[test]
fn a_mismatch_under_a_redex_head_is_spelled_at_the_expression() {
    let cases = [
        (
            "theorem bad(f: Nat → Nat, P: Nat → Type, n: Nat, h: P(n)): True { \
             let post = λ (u: Nat) => P(u); let x: post(f(n)) = h; trivial }",
            "h",
            "`P(n)`, but `P(f(n))`",
        ),
        (
            "theorem bad(f: Nat → Nat, P: Nat → Type, n: Nat, h: P(n)): True { \
             let post = λ (u: Nat) (v: Nat) => P(v); let x: post(n, f(n)) = h; trivial }",
            "h",
            "`P(n)`, but `P(f(n))`",
        ),
        (
            "theorem bad(f: Nat → Nat, P: Nat → Type, n: Nat, h: P(n) ∧ True): True { \
             let post = λ (u: Nat) => P(u); let x: post(f(n)) ∧ True = h; trivial }",
            "h",
            "`And<P(n), True>`, but `And<P(f(n)), True>`",
        ),
        (
            "theorem bad(f: Nat → Nat, P: Nat → Type, Q: Type, q: Q): True { \
             weaken_like(λ (s: Nat) => P(f(s)) ∧ Q, λ (s: Nat) => P(s), λ s held => ⟨held, q⟩) }",
            "held",
            "`P(s)`, but `P(f(s))`",
        ),
    ];
    for (case, at, types) in cases {
        let src = format!("{REDEX}{case}\n");
        let r = reject(&src);
        let rendered = r.render(&src);
        assert!(rendered.contains(&format!("this has type {types} is expected here")), "{case}\n{rendered}");
        assert!(!rendered.contains("the kernel rejected"), "{case}\n{rendered}");
        let ElabError::Elab { span, .. } = r else { panic!("{case}: expected an elaborator error: {r}") };
        let start = src.rfind(case).unwrap() + case.find('{').unwrap();
        assert!(span.start as usize > start, "{case}: reported outside the body\n{rendered}");
        assert_eq!(&src[span.start as usize..span.end as usize], at, "{case}\n{rendered}");
    }
}

/// **Control for the redex spelling.** The same shapes at the right type are
/// accepted: the contraction is the display's, and checking never sees it.
#[test]
fn a_redex_head_of_the_right_type_is_accepted() {
    ok(&format!("{REDEX}\
        theorem good(f: Nat → Nat, P: Nat → Type, n: Nat, h: P(f(n))): True {{ \
        let post = λ (u: Nat) => P(u); let x: post(f(n)) = h; trivial }}\n\
        theorem good_binder(P: Nat → Type, Q: Type, q: Q): True {{ \
        weaken_like(λ (s: Nat) => P(s) ∧ Q, λ (s: Nat) => P(s), λ s held => ⟨held, q⟩) }}\n"));
}

/// **The net under the class** (`issues/elab-accepts-conjunction-for-equation.md`).
/// A refusal no recorded site explains is a route that placed a term without
/// comparing or recording it; each one was found by bisecting a bare
/// `NotConvertible`. The filed case is re-opened here as it stood before
/// #168 — the inferred argument of `sym`/`trans` owing no check — and the
/// kernel's locator must still name the refused term and both types, flag
/// the refusal as unrecorded, and leave the verdict and the span the gate's.
#[test]
fn an_unrecorded_refusal_names_the_refused_term_and_both_types() {
    const BOTH: &str = "record Both<P, Q> { l: P, r: Q }\n";
    let cases = [
        ("theorem bad4(a, b: Nat, p: Both<a = b, b = b>): b = a { sym(p) }", "theorem bad4("),
        ("theorem bad2(a, b, c: Nat, p: Both<a = b, b = b>, q: b = c): a = c { trans(p, q) }", "theorem bad2("),
    ];
    for (case, head) in cases {
        let src = format!("{BOTH}{case}\n");
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.forget_owed_argument_checks();
        let r = e.elab_source(&src).expect_err("refused");
        let rendered = r.render(&src);
        let ElabError::Kernel { span, err, site, .. } = &r else { panic!("{case}: expected the kernel's refusal: {rendered}") };
        assert_eq!(*site, KernelSite::Unrecorded, "{case}\n{rendered}");
        assert_eq!(*err, TypeError::NotConvertible, "{case}\n{rendered}");
        assert!(src[span.start as usize..].starts_with(head), "{case}: the span stays the declaration's\n{rendered}");
        assert!(
            rendered.contains("no checking site recorded this refusal: the kernel refused `p`, \
                               which has type `Both<a = b, b = b>`, where `a = b` is expected"),
            "{case}\n{rendered}"
        );
    }
}

/// **Control for the net.** With the route recording, the same refusals are
/// the elaborator's, at `p`, and nothing is called unrecorded.
#[test]
fn a_recorded_site_still_reports_at_the_argument() {
    let src = "record Both<P, Q> { l: P, r: Q }\n\
               theorem bad4(a, b: Nat, p: Both<a = b, b = b>): b = a { sym(p) }\n";
    let r = reject(src);
    let rendered = r.render(src);
    let ElabError::Elab { span, .. } = &r else { panic!("expected the elaborator's report: {rendered}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "p", "{rendered}");
    assert!(rendered.contains("this has type `Both<a = b, b = b>`, but `a = b` is expected here"), "{rendered}");
}
