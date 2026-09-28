//! Diagnostics print a kernel type back as **surface** syntax
//! (`docs/surface-type-display-design.md`,
//! `issues/le-diagnostics-print-raw-el.md`).
//!
//! Every test here pins *rendered message text*, because the defect was never
//! "no error was reported" — it was that the error was unreadable.
//!
//! Two axes of `docs/testing-generated-terms.md` carry the weight, and both are
//! forced by the subject rather than chosen for tidiness. **Open arguments:** a
//! closed `Le(3, 10)` normalises to `True` and never reaches this code at all,
//! so only an open relation exercises it. **A parameterized inductive:** the
//! lowering that produced the several-hundred-column messages is `Wf(Σ…)`, and a
//! monomorphic declaration's lowering is small enough to hide how bad raw was.
//! The negative controls — a term the speller refuses, and more refusals than
//! its budget tolerates — live beside the speller itself, in
//! `crates/elab/src/display.rs`, because the surface language makes an
//! unspellable type hard to *write*.

use heather_elab::{ElabError, Elaborator};

/// `add`, which the prelude does not define.
const ADD: &str = "
fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => Succ(add(k, n)) } }
";

fn reject(src: &str) -> ElabError {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err,
    }
}

fn rendered(src: &str) -> String {
    let e = reject(src);
    e.render(src)
}

fn goals(src: &str) -> Vec<(String, Vec<(String, String)>)> {
    match reject(src) {
        ElabError::UnsolvedGoals { goals, .. } => {
            goals.into_iter().map(|g| (g.statement, g.context)).collect()
        }
        other => panic!("expected an unsolved-goal listing, got {other}"),
    }
}

/// A propositional relation is a `fn … -> Type` (`docs/nat-order-design.md`
/// §1), so at **open** arguments its type is `El(Le(n)(m))` — stuck as an `El`
/// irreducibly, which is why [[goal-display-decodes]]' reader cannot help. The
/// filed symptom, verbatim: `trivial` at a comparison used to print
/// `El[0](app(app(u55^{·^2}; …)))`.
#[test]
fn a_relation_at_open_arguments_prints_as_a_call() {
    let src = r#"
inductive Void { }
fn Le(n: Nat) -> Nat -> Type {
    match n {
        Zero => λ (m: Nat) => True,
        Succ(k) => λ (m: Nat) => match m { Zero => Void, Succ(l) => Le(k)(l) },
    }
}
theorem t(n, m: Nat): Le(n)(m) { trivial }
"#;
    let r = rendered(src);
    assert!(r.contains("`trivial` proves `True`, but `Le(n, m)` is expected here"), "{r}");
    assert!(!r.contains("El["), "no raw encoding should survive: {r}");
}

/// The same type through the *other* display site: the ordinary unfilled-goal
/// listing, which is the message a proof under construction sees most often.
#[test]
fn a_goal_statement_at_a_relation_prints_as_a_call() {
    let src = r#"
inductive Void { }
fn Le(n: Nat) -> Nat -> Type {
    match n {
        Zero => λ (m: Nat) => True,
        Succ(k) => λ (m: Nat) => match m { Zero => Void, Succ(l) => Le(k)(l) },
    }
}
theorem t(n, m: Nat): Le(n)(m) { ?g }
"#;
    let gs = goals(src);
    assert_eq!(gs[0].0, "Le(n, m)");
}

/// The second customer on the issue: an equation between two calls over a
/// parameterized inductive. Three things are being fixed at once — the `Id`
/// spells as `=` (it was never `El`-headed, so the reader declined it in its
/// first line), each call spells as a call with its *implicit* type argument
/// dropped, and each context binder spells as its declaration's name instead of
/// its `Wf(Σ…)` lowering.
#[test]
fn an_equation_between_calls_over_an_inductive_prints_as_surface() {
    let src = r#"
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
fn append<A>(xs: List<A>, ys: List<A>) -> List<A> {
    match xs { Nil => ys, Cons(h, t) => Cons(h, append(t, ys)) }
}
fn len<A>(xs: List<A>) -> Nat {
    match xs { Nil => 0, Cons(h, t) => Succ(len(t)) }
}
theorem len_append<A>(xs, ys: List<A>): len(append(xs, ys)) = add(len(xs), len(ys)) {
    match xs { Nil => ?, Cons(h, t) => ? }
}
"#;
    let gs = goals(&format!("{ADD}{src}"));
    // The `Nil` arm: the motive is instantiated at a canonical nullary
    // constructor, so the constructor value spells too.
    assert_eq!(gs[0].0, "len(append(Nil, ys)) = add(len(Nil), len(ys))");
    // The `Cons` arm's motive is instantiated at the *neutral* summand value,
    // whose fields are projections. The typed arm aliases recover their
    // written names, including the recursive child at the open element type.
    assert_eq!(gs[1].0, "len(append(Cons(h, t), ys)) = add(len(Cons(h, t)), len(ys))");
    for g in &gs {
        assert!(
            g.1.iter().any(|(n, ty)| n == "xs" && ty == "List<A>"),
            "context should name the declaration and its recovered argument: {:?}",
            g.1
        );
        assert!(
            !g.1.iter().any(|(_, ty)| ty.contains("Wf[")),
            "no lowering should survive: {:?}",
            g.1
        );
    }
    // An erased type parameter is a `Ty` binder, and a value at it is `El(x)`.
    assert!(gs[1].1.iter().any(|(n, ty)| n == "A" && ty == "Type<0>"), "{:?}", gs[1].1);
    assert!(gs[1].1.iter().any(|(n, ty)| n == "h" && ty == "A"), "{:?}", gs[1].1);
}

/// Numerals are decimal, not a `Succ` tower, and a `Vec` is its surface
/// bracket form. Both are one-line spellings whose raw forms are the reason
/// this module exists.
#[test]
fn numerals_and_vectors_spell() {
    let gs = goals(&format!("{ADD}theorem t(n: Nat): add(3, n) = n {{ ?g }}"));
    assert_eq!(gs[0].0, "add(3, n) = n");

    let gs = goals("fn f(n: Nat) -> [Nat; n] { ?g }");
    assert_eq!(gs[0].0, "[Nat; n]");
}

/// A function type spells as an arrow, and its binder is named only when the
/// codomain uses it — the kernel `Π` does not record the written name, so a
/// dependent one gets a fresh one that does not shadow anything in scope.
#[test]
fn function_types_spell_as_arrows() {
    let gs = goals("fn f() -> Nat -> Nat { ?g }");
    assert_eq!(gs[0].0, "Nat -> Nat");
}

/// The reader keeps precedence where a head exists (design §3): an alias for
/// `Nat` prints as `Nat`, which is what the type *is*, not as the alias.
/// [[goal-display-decodes]]' pin, restated here because the ordering is now a
/// decision rather than the only option.
#[test]
fn the_reader_still_wins_where_a_head_exists() {
    let gs = goals(
        r#"
        fn N(v: Nat) -> Type { Nat }
        theorem decoded(v: Nat): N(v) { ?g }
        "#,
    );
    assert_eq!(gs[0].0, "Nat");
}

#[test]
fn registered_record_projections_keep_field_and_receiver_names() {
    let src = r#"
record Inner { value: Nat, valid: value = value }
record Outer { left: Inner, right: Inner, valid: left.value = right.value }
theorem compare(x: Outer): x.left.value = x.right.value { ?comparison }
"#;
    let reports = goals(src);
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].0, "x.left.value = x.right.value");
}

#[test]
fn record_projection_display_respects_a_nested_binder() {
    let src = r#"
record Entry { first: Nat, second: Nat, valid: first = second }
theorem compare(x: Entry): (y: Entry) → x.second = y.first { ?comparison }
"#;
    let reports = goals(src);
    assert_eq!(reports.len(), 1);
    let statement = &reports[0].0;
    assert!(statement.contains("x.second"), "{statement}");
    assert!(
        !statement.contains("app(") && !statement.contains("Σ"),
        "{statement}"
    );
    assert!(statement.contains(".first"), "{statement}");
}

/// A parameterized inductive **under a binder**. The walk recovers a
/// declaration's type arguments by strengthening the field types out of its
/// lowering back to the context it holds; a binder the walk has descended
/// under is not in that context, so the variable addressed nothing and the
/// kernel aborted the process — `local variable N escapes the substitution's
/// target entries` — instead of the diagnostic being printed
/// (issues/pi-codomain-record-mismatch-panics-kernel.md).
///
/// The axes are forced, and each one alone hides it
/// (`docs/testing-generated-terms.md`): the carrier must be **open**, or there
/// is no `Π` whose codomain mentions its binder; and the mismatch must be a
/// **refusal**, because the crash was in rendering the refusal and a body that
/// checks never renders one.
#[test]
fn a_parameterized_inductive_under_a_binder_renders_instead_of_aborting() {
    const BOTH: &str = "record Both<P, Q> { left: P, right: Q }\n";
    // The argument genuinely mentions the binder, so it does not strengthen
    // back to the context and the honest ellipsis is the answer. What matters
    // is that there *is* an answer.
    let msg = rendered(&format!(
        "{BOTH}theorem dep<A>(P: A -> Type, R: Type, h: R): (a: A) -> Both<P(a), R> {{ h }}"
    ));
    assert!(
        msg.contains("this has type `R`, but `(x: A) -> Both<…>` is expected here"),
        "{msg}"
    );
    // …and where the arguments do *not* mention the binder they are recovered
    // and spelled, which the old code could not do either: it strengthened
    // against a context short by the binder, so an argument mentioning any
    // outer variable fell off the end of the substitution too.
    let msg = rendered(&format!(
        "{BOTH}theorem indep<A>(P: Type, R: Type, h: Nat): (a: A) -> Both<P, R> {{ h }}"
    ));
    assert!(
        msg.contains("this has type `Nat`, but `A -> Both<P, R>` is expected here"),
        "{msg}"
    );
    // The control at zero binders, which always worked and must not move.
    let msg = rendered(&format!(
        "{BOTH}theorem flat(P: Type, R: Type, h: Nat): Both<P, R> {{ h }}"
    ));
    assert!(
        msg.contains("this has type `Nat`, but `Both<P, R>` is expected here"),
        "{msg}"
    );
}
