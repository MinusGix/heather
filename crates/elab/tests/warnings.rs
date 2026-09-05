//! The warning channel and its first customer
//! (`docs/diagnostic-warnings-design.md`).
//!
//! Two things are under test and they are independent. The **channel**: a
//! diagnostic that is not a failure, said about a file that checks, without
//! disturbing `check_source`'s "empty means the file is good" contract or the
//! exit status. The **customer**: an arm that can never be reached, which the
//! pattern compiler has always known about — `Compile.uses[i] == 0` is the
//! census §5 computes for sharing — and until now had nowhere to say.

use heather_elab::{Elaborator, Lint, LintProfile};

const TOK: &str = "
inductive Tok { TA, TB }
inductive P { Mk(a: Tok, b: Tok) }
";
const LIST_DECL: &str = "inductive List<A> { Nil, Cons(head: A, tail: List<A>) }\n";
const LIST: &str = r#"
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
instance<A>(n: Nat) CollectionLiteral<List<A>>(n) {
    element := A,
    fromLiteral := λ (xs: [A; n]) =>
        xs.fold(Nil<A>, λ (head: A) (tail: List<A>) => Cons(head, tail)),
}
"#;

fn with_standard_list() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("list", LIST).expect("canonical list module");
    e
}

/// Check a good file and return its warnings' messages.
fn warns(src: &str) -> Vec<String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!("{TOK}{src}");
    let errs = e.check_source(&src);
    assert!(errs.is_empty(), "expected a clean check, got: {}", errs[0].render(&src));
    e.take_warnings().into_iter().map(|w| w.msg).collect()
}

// -- the channel -----------------------------------------------------------

/// §2: the contract `check_source` has always had is untouched. A file with a
/// warning still returns **no errors**, which is what every caller in the tree
/// reads as "this file is good" — the cache's end-to-end asserts, the bench
/// fixtures, the CLI's `ok` line.
#[test]
fn a_warning_does_not_make_a_good_file_bad() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!("{TOK}fn f(t: Tok) -> Nat {{ match t {{ TA => 0, TB => 1, _ => 2 }} }}");
    assert!(e.check_source(&src).is_empty(), "the file checks");
    assert_eq!(e.take_warnings().len(), 1, "and it warns");
}

/// §3: draining, not borrowing. The CLI renders each module against its own
/// source, so a warning must leave with the text its span indexes into.
#[test]
fn take_warnings_drains() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!("{TOK}fn f(t: Tok) -> Nat {{ match t {{ TA => 0, TB => 1, _ => 2 }} }}");
    e.check_source(&src);
    assert_eq!(e.take_warnings().len(), 1);
    assert!(e.take_warnings().is_empty(), "the second take sees nothing");
}

/// The prelude is elaborated inside `with_prelude`, so a warning raised there
/// would be pre-loaded into every session and attributed to the first file
/// anyone checks. It is clean, and this is the assertion that keeps it clean.
#[test]
fn a_fresh_elaborator_carries_no_warnings() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert!(e.take_warnings().is_empty());
}

/// §4: a declaration that fails says nothing. Its warnings are as speculative
/// as the rest of it — the same rule, at the same site, as its pending
/// derivations.
#[test]
fn a_failed_declaration_raises_no_warnings() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    // The `_` arm is unreachable (so `prepare_arms` warns) and the first arm's
    // body is an unbound name (so the declaration then fails). Order matters:
    // the pass runs before any arm body is elaborated, so the warning really
    // is raised and really is withdrawn.
    let src = format!("{TOK}fn f(t: Tok) -> Nat {{ match t {{ TA => nope, TB => 1, _ => 2 }} }}");
    let errs = e.check_source(&src);
    assert_eq!(errs.len(), 1, "the declaration fails");
    assert!(e.take_warnings().is_empty(), "and takes its warning with it");
}

/// The other half of the same rule: `check_source` recovers per declaration,
/// so a *later* failure must not withdraw an *earlier* declaration's warning.
#[test]
fn a_later_failure_keeps_an_earlier_declarations_warning() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!(
        "{TOK}
fn good(t: Tok) -> Nat {{ match t {{ TA => 0, TB => 1, _ => 2 }} }}
fn bad(t: Tok) -> Nat {{ nope }}
"
    );
    assert_eq!(e.check_source(&src).len(), 1, "the second declaration fails");
    let ws = e.take_warnings();
    assert_eq!(ws.len(), 1, "the first declaration's warning stands: {ws:?}");
}

/// §5: the rendering is the error renderer with one word changed, so a reader
/// meets one shape. The span is the arm's, not the whole `match`'s.
#[test]
fn a_warning_renders_like_an_error_with_its_severity() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!("{TOK}fn f(t: Tok) -> Nat {{ match t {{ TA => 0, TB => 1, _ => 2 }} }}");
    e.check_source(&src);
    let w = e.take_warnings().pop().expect("a warning");
    let snip = w.render_snippet(&src, "f.hthr");
    assert!(snip.starts_with("warning: "), "{snip}");
    assert!(snip.contains("f.hthr:4:"), "the location line: {snip}");
    assert!(snip.contains("^^^^^^"), "the caret line: {snip}");
    assert!(w.render(&src).contains("4:"), "the compact form carries a position");
}

// -- the customer: unreachable arms ---------------------------------------

/// The redundant `_`, which the pattern compiler silently **drops** today.
#[test]
fn a_dead_default_arm_is_reported() {
    let ws = warns("fn f(t: Tok) -> Nat { match t { TA => 0, TB => 1, _ => 2 } }");
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert!(ws[0].contains("`_` arm can never be reached"), "{}", ws[0]);
    assert!(ws[0].contains("already cover every constructor"), "{}", ws[0]);
}

#[test]
fn warnings_carry_a_stable_lint_identity() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!("{TOK}fn f(t: Tok) -> Nat {{ match t {{ TA => 0, TB => 1, _ => 2 }} }}");
    assert!(e.check_source(&src).is_empty());
    let w = e.take_warnings().pop().expect("a warning");
    assert_eq!(w.lint, Lint::UnreachableMatchArm);
    assert_eq!(w.lint.name(), "unreachable-match-arm");
}

#[test]
fn a_finite_manual_list_spine_recommends_list_literal_syntax_once() {
    let mut e = with_standard_list();
    let src = r#"
        import list;
        fn xs() -> List<Nat> { Cons(1, Cons(2, Nil)) }
    "#;
    e.elab_module_source("manual_list_warning", src).expect("source checks");
    let warnings = e.take_warnings();
    let list_warnings = warnings
        .iter()
        .filter(|warning| warning.lint == Lint::ManualListConstruction)
        .collect::<Vec<_>>();
    assert_eq!(list_warnings.len(), 1, "one warning for the outer spine: {warnings:?}");
    assert_eq!(list_warnings[0].lint.name(), "manual-list-construction");
    assert!(list_warnings[0].msg.contains("write `[…]` instead"));
}

#[test]
fn recursive_list_construction_and_literal_syntax_do_not_warn() {
    let mut e = with_standard_list();
    let src = r#"
        import list;
        fn keep<A>(x: A, tail: List<A>) -> List<A> { Cons(x, tail) }
        fn empty<A>() -> List<A> { Nil }
        fn literal() -> List<Nat> { [1, 2] }
    "#;
    e.elab_module_source("recursive_list_no_warning", src).expect("source checks");
    assert!(
        e.take_warnings().iter().all(|warning| warning.lint != Lint::ManualListConstruction),
        "open constructor work, bare Nil, and the preferred syntax stay quiet",
    );
}

#[test]
fn an_inferred_finite_list_spine_is_also_concrete_enough_to_warn() {
    let mut e = with_standard_list();
    let src = r#"
        import list;
        fn xs() -> List<Nat> { let inferred = Cons(1, Cons(2, Nil)); inferred }
    "#;
    e.elab_module_source("inferred_list_warning", src).expect("source checks");
    let warnings = e.take_warnings();
    assert_eq!(
        warnings.iter().filter(|warning| warning.lint == Lint::ManualListConstruction).count(),
        1,
        "the inferred outer spine is the one finding: {warnings:?}",
    );
}

#[test]
fn a_nominal_list_impostor_does_not_receive_the_standard_list_lint() {
    let mut e = with_standard_list();
    e.elab_module_source("other", LIST).expect("unrelated list module");
    let src = r#"
        import other;
        fn xs() -> other::List<Nat> { Cons(1, Cons(2, Nil)) }
    "#;
    e.elab_module_source("impostor_list_warning", src).expect("source checks");
    assert!(
        e.take_warnings().iter().all(|warning| warning.lint != Lint::ManualListConstruction),
        "a nominally unrelated declaration must not inherit standard-list syntax policy",
    );
}

#[test]
fn the_standard_list_without_literal_opt_in_receives_no_unusable_suggestion() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("list", LIST_DECL).expect("canonical list declaration");
    let src = r#"
        import list;
        fn xs() -> List<Nat> { Cons(1, Cons(2, Nil)) }
    "#;
    e.elab_module_source("list_without_literal_instance", src).expect("source checks");
    assert!(
        e.take_warnings().iter().all(|warning| warning.lint != Lint::ManualListConstruction),
        "a lint must not suggest syntax the declaration has not opted into",
    );
}

// -- registered source lints ----------------------------------------------

#[test]
fn an_immediately_applied_function_match_is_reported() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn old(n: Nat) -> Nat -> Nat {
        λ m => match n as λ z => Nat -> Nat {
            Zero => λ x => x,
            Succ(k) => λ x => x,
        }(m)
    }";
    assert!(e.check_source(src).is_empty());
    let ws = e.take_warnings();
    let w = ws
        .iter()
        .find(|w| w.lint == Lint::MatchFunctionApplication)
        .expect("the match-function lint");
    assert_eq!(w.lint.name(), "match-function-application");
    assert!(w.msg.contains("checking position"), "{}", w.msg);
    assert!(w.msg.contains("motive may be inferable"), "{}", w.msg);
}

#[test]
fn a_match_used_as_a_function_value_is_not_reported() {
    let direct = "fn kept(n: Nat) -> Nat -> Nat {
        match n as λ z => Nat -> Nat { Zero => λ x => x, Succ(k) => λ x => x }
    }";
    let nonbinder = "fn applied(n: Nat) -> Nat -> Nat {
        λ m => match n as λ z => Nat -> Nat {
            Zero => λ x => x, Succ(k) => λ x => x
        }(0)
    }";
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert!(e.check_source(direct).is_empty());
    assert!(e.check_source(nonbinder).is_empty());
    assert!(
        e.take_warnings().iter().all(|w| w.lint != Lint::MatchFunctionApplication),
        "neither control is an immediately applied function match"
    );
}

#[test]
fn spaced_prefix_negation_is_reported_but_comments_are_preserved() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "
        inductive Empty {}
        fn Not(P: Type) → Type { P → Empty }
        fn spaced(P: Type, h: ¬ P) → ¬P { h }
        fn documented(P: Type, h: ¬ // why this hypothesis is negative
            P) → ¬P { h }
    ";
    assert!(e.check_source(src).is_empty());
    let ws = e.take_warnings();
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert_eq!(ws[0].lint, Lint::TightNegationSpacing);
    assert_eq!(ws[0].lint.name(), "tight-negation-spacing");
    let fix = ws[0].fix.as_ref().expect("spacing has a mechanical fix");
    assert_eq!(&src[fix.span.start..fix.span.end], " ");
    assert_eq!(fix.replacement, "");
}

#[test]
fn unicode_spelling_is_a_stdlib_profile_not_a_language_rule() {
    let src = "// ASCII examples remain useful: fun x -> x\nfn id(n: Nat) -> Nat { (fun (x: Nat) => x)(n) }";
    let mut ordinary = Elaborator::with_prelude().expect("prelude");
    let errs = ordinary.check_source(src);
    assert!(errs.is_empty(), "{}", errs[0].render(src));
    assert!(ordinary.take_warnings().is_empty());

    let mut stdlib = Elaborator::with_prelude().expect("prelude");
    stdlib.set_lint_profile(LintProfile::Stdlib);
    let errs = stdlib.check_source(src);
    assert!(errs.is_empty(), "{}", errs[0].render(src));
    let ws = stdlib.take_warnings();
    assert_eq!(ws.len(), 2, "{ws:?}");
    assert!(ws.iter().all(|w| w.lint == Lint::StdlibUnicodeSpelling));
    assert!(ws.iter().any(|w| w.msg.contains("replace `->` with `→`")));
    assert!(ws.iter().any(|w| w.msg.contains("replace `fun` with `λ`")));
    assert!(ws.iter().all(|w| w.fix.is_some()), "alias replacements are structured fixes");
}

#[test]
fn consecutive_direct_calls_prefer_one_argument_list() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn apply(f: Nat → Nat → Nat) → Nat { f(0)(1) }";
    assert!(e.check_source(src).is_empty());
    let ws = e.take_warnings();
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert_eq!(ws[0].lint, Lint::NestedCall);
    assert_eq!(ws[0].lint.name(), "nested-call");
    assert!(ws[0].msg.contains("`f(a, b)`"));
}

#[test]
fn template_emission_does_not_suggest_invalid_call_flattening() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "meta fn identity(g: Ctx) -> Code(g |- Nat -> Nat) {
        code { fun (n: Nat) => n }
    }
    fn use_it(n: Nat) -> Nat { emit_code(identity)(n) }";
    let errors = e.check_source(src);
    assert!(errors.is_empty(), "{errors:?}");
    assert!(e.take_warnings().iter().all(|w| w.lint != Lint::NestedCall));
}

#[test]
fn staged_or_computed_function_values_are_not_nested_call_style() {
    let src = "
        fn staged(f: Nat → Nat → Nat) → Nat { let g = f(0); g(1) }
        fn computed() → Nat { (λ (x: Nat) => λ (y: Nat) => x)(0)(1) }
    ";
    let mut e = Elaborator::with_prelude().expect("prelude");
    let errs = e.check_source(src);
    assert!(errs.is_empty(), "{}", errs[0].render(src));
    assert!(e.take_warnings().is_empty());
}

#[test]
fn unused_pattern_payloads_are_identity_aware_and_fixable() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!(
        "{TOK}
         fn one(p: P) → Nat {{
             match p {{ Mk(x, y) => match x {{ TA => 0, TB => 1 }} }}
         }}
         fn shadowed(p: P) → Nat {{
             match p {{ Mk(x, y) => (λ (x: Nat) => x)(0) }}
         }}"
    );
    assert!(e.check_source(&src).is_empty());
    let ws = e
        .take_warnings()
        .into_iter()
        .filter(|w| w.lint == Lint::UnusedPatternBinder)
        .collect::<Vec<_>>();
    assert_eq!(ws.len(), 3, "{ws:?}");
    assert_eq!(ws.iter().filter(|w| w.msg.contains("`y`")).count(), 2);
    assert_eq!(ws.iter().filter(|w| w.msg.contains("`x`")).count(), 1);
    assert!(ws.iter().all(|w| w.fix.as_ref().is_some_and(|f| f.replacement == "_")));
}

#[test]
fn an_unused_explicit_induction_hypothesis_has_a_distinct_warning() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn predecessor(n: Nat) → Nat {
        match n { Zero => 0, Succ(k, ih) => k }
    }";
    assert!(e.check_source(src).is_empty());
    let ws = e.take_warnings();
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert_eq!(ws[0].lint, Lint::UnusedPatternBinder);
    assert_eq!(ws[0].lint.name(), "unused-pattern-binder");
    assert!(ws[0].msg.contains("induction hypothesis `ih`"), "{}", ws[0].msg);
    assert!(ws[0].msg.contains("case analysis"), "{}", ws[0].msg);
}

#[test]
fn operator_fallback_warns_only_after_a_known_carrier_misses_designation() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "
        inductive A { A0 }
        inductive B { B0 }
        fn add(a: A, b: A) → A { a }
        fn add_b(a: B, b: B) → B { a }
        designation + at B := add_b
        fn fallback(a: A, b: A) → A { a + b }
        designation + at A := add
        fn designated(a: A, b: A) → A { a + b }
    ";
    assert!(e.check_source(src).is_empty());
    let ws = e
        .take_warnings()
        .into_iter()
        .filter(|w| w.lint == Lint::OperatorFallback)
        .collect::<Vec<_>>();
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert_eq!(ws[0].lint.name(), "operator-fallback");
    assert!(ws[0].msg.contains("no designation at `A`"), "{}", ws[0].msg);
    assert!(ws[0].msg.contains("fallback `add`"), "{}", ws[0].msg);
    assert!(ws[0].msg.contains("designation + at A := add"), "{}", ws[0].msg);
}

#[test]
fn compatibility_fallback_without_any_designation_remains_silent() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn add(a: Nat, b: Nat) → Nat { a }
               fn old_surface(a: Nat, b: Nat) → Nat { a + b }";
    assert!(e.check_source(src).is_empty());
    assert!(e.take_warnings().iter().all(|w| w.lint != Lint::OperatorFallback));
}

#[test]
fn a_match_motive_verified_redundant_in_checking_position_has_an_exact_fix() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn choose(n: Nat) → Nat {
        match n as λ z => Nat { Zero => 0, Succ(k) => k }
    }";
    assert!(e.check_source(src).is_empty());
    let ws = e
        .take_warnings()
        .into_iter()
        .filter(|w| w.lint == Lint::RedundantMatchMotive)
        .collect::<Vec<_>>();
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert_eq!(ws[0].lint.name(), "redundant-match-motive");
    let fix = ws[0].fix.as_ref().expect("omission is an exact source edit");
    assert!(src[fix.span.start..fix.span.end].contains("as λ z => Nat"));
    let fixed = format!("{}{}{}", &src[..fix.span.start], fix.replacement, &src[fix.span.end..]);
    let mut verify = Elaborator::with_prelude().expect("prelude");
    assert!(verify.check_source(&fixed).is_empty(), "the suggested omission checks");
}

#[test]
fn a_motive_required_for_inference_is_not_called_redundant() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "fn choose(n: Nat) → Nat {
        let answer = match n as λ z => Nat { Zero => 0, Succ(k) => k };
        answer
    }";
    assert!(e.check_source(src).is_empty());
    assert!(e.take_warnings().iter().all(|w| w.lint != Lint::RedundantMatchMotive));
}

/// A `_` that stands for a constructor with no arm of its own is the whole
/// point of the feature and is not a warning. Without this control, "warn on
/// every `_`" would pass the test above.
#[test]
fn a_working_default_arm_is_silent() {
    assert!(warns("fn f(t: Tok) -> Nat { match t { TA => 0, _ => 2 } }").is_empty());
    // …as is a `match` with no `_` at all, which never enters the pass.
    assert!(warns("fn g(t: Tok) -> Nat { match t { TA => 0, TB => 1 } }").is_empty());
}

/// The other shape the redundancy issue lists: a row shadowed by an earlier
/// one, which needs the deep-pattern matrix to arise at all (a shallow
/// duplicate is the existing `duplicate arm` **error**).
#[test]
fn a_shadowed_deep_row_is_reported() {
    let ws = warns(
        "fn f(p: P) -> Nat {
             match p { Mk(TA, y) => 0, Mk(x, y) => 1, Mk(TB, TB) => 2 } }",
    );
    let w = ws.iter().find(|w| w.contains("can never be reached")).expect("dead arm warning");
    assert!(w.contains("`Mk` arm can never be reached"), "{w}");
    assert!(w.contains("an earlier `Mk` arm"), "{w}");
    // What the warning is *for*: a body that never runs was also never
    // checked, so the silence hid a second thing.
    assert!(w.contains("never checked"), "{w}");
}

/// §7.1, and the control the whole `generated` flag exists for: the pattern
/// compiler emits `_` arms of its own, and re-runs this pass over them. Here
/// every written arm is reachable, while the level generated for the first
/// column covers `TA`, `TB` **and** a fallthrough — so without the flag this
/// file reports a `_` arm nobody wrote, pointed at the whole `match`.
/// Verified by removing the guard and watching it fire.
#[test]
fn a_generated_levels_own_default_arm_is_not_reported() {
    assert!(
        warns(
            "fn h(p: P) -> Nat {
                 match p { Mk(TA, TA) => 0, Mk(TB, TA) => 1, Mk(x, y) => 2 } }",
        )
        .iter()
        .all(|w| !w.contains("can never be reached"))
    );
}

/// The message names the form the writer used, like every other message that
/// names one (issues/diagnostics-name-the-written-form.md).
#[test]
fn the_message_names_the_written_form() {
    let ws = warns("fn f(t: Tok) -> Nat { split t; on TA := 0; on TB := 1; on _ := 2; }");
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert!(ws[0].contains("this `split` means"), "{}", ws[0]);
}

/// §4.1: a span into generated text does not index into any file a reader has.
/// A `datarepr`'s emission is elaborated *inside* an ordinary check of the
/// declaration that owns it, so a warning raised there would be rendered
/// against the user's source and point its caret at an unrelated line.
#[test]
fn generated_source_raises_no_warnings() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(TOK).expect("the inductives");
    let dead = "fn f(t: Tok) -> Nat { match t { TA => 0, TB => 1, _ => 2 } }";
    e.elab_generated_source(dead).expect("the generated declaration checks");
    assert!(e.take_warnings().is_empty(), "generated code warns nobody");
    // The control: the very same text as *user* source does warn, so what is
    // being tested is the boundary and not the example.
    e.elab_source("fn g(t: Tok) -> Nat { match t { TA => 0, TB => 1, _ => 2 } }")
        .expect("the user declaration checks");
    assert_eq!(e.take_warnings().len(), 1);
}
