//! Acceptance for a record type's **partial application**, against
//! `issues/record-type-partial-application.md` and
//! `docs/record-type-partial-application.md` §4. Two siblings share this
//! round's disambiguator, each pointed a different way:
//! `crates/elab/tests/constructor_values.rs` (η-expand the *constructor* at an
//! expected Π) and `crates/elab/tests/record_type_values.rs` (read the *type
//! former* at an expected universe). This is the intersection of the two — an
//! expected Π whose ultimate codomain is a universe — and the reason the
//! showcases carried three do-nothing `fn` wrappers.
//!
//! The axes `docs/testing-generated-terms.md` asks for: the fixed prefix is a
//! *literal* in one test and a *neutral* in the next, the element type is
//! **open** in `an_open_element_type_comes_along`, every positive test
//! *inhabits* the type it built rather than only elaborating it, and the
//! constructor reading of the same record in the same file is the negative
//! control.

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

// The issue's repro, and the wrapper it existed to avoid. `Grammar` bare is
// the whole telescope abstracted; the wrapper is the same thing written out.
// Elaborating them is not the test — the last two theorems are: one inhabits
// the type built from the record name, the other transports an inhabitant of
// the *wrapper*'s version into it, so the two readings are shown to agree
// rather than merely both to check.
#[test]
fn a_record_type_is_a_relation() {
    elab(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }

        fn takes_relation(rel: Nat -> Nat -> Type) -> Type { rel(0, 1) }
        fn GrammarSpec(level: Nat, value: Nat) -> Type { Grammar(level, value) }

        fn direct() -> Type { takes_relation(Grammar) }
        fn wrapped() -> Type { takes_relation(GrammarSpec) }

        theorem via_wrapper(): takes_relation(GrammarSpec) { Grammar { at_level: refl } }
        theorem via_record(): takes_relation(Grammar) { Grammar { at_level: refl } }
        theorem agree(): takes_relation(Grammar) { via_wrapper() }
        theorem agree_back(): takes_relation(GrammarSpec) { via_record() }
        "#,
    );
}

// Partial application: the prefix is written, the rest is abstracted. At a
// **literal** prefix and at a **neutral** one, since a literal can be
// evaluated away and a neutral cannot.
#[test]
fn a_prefix_may_be_written() {
    elab(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }

        fn Fam(dom: Nat -> Type) -> Type { (v: Nat) -> dom(v) }

        // literal prefix
        fn at_zero() -> Type { Fam(Grammar(0)) }
        theorem all_at_zero(): Fam(Grammar(0)) { λ v => Grammar { at_level: refl } }

        // neutral prefix
        fn at_level(level: Nat) -> Type { Fam(Grammar(level)) }
        theorem all_at_level(level: Nat): Fam(Grammar(level)) { λ v => Grammar { at_level: refl } }

        // the two agree where the neutral is instantiated
        theorem instantiated(): Fam(Grammar(0)) { all_at_level(0) }
        "#,
    );
}

// **The showcase shape**: the relation slot of `lib/std/parser/parser_contracts.hthr`'s
// `Certified` is `(source) -> Cursor<T>(source) -> Cursor<T>(source) -> A -> Type`,
// so the second domain's type *depends* on the first binder. The η-expansion
// peels the spine binder by binder for exactly this reason; a peel that read
// every domain in the ambient context would not see `Slot(n)` at all.
#[test]
fn a_dependent_domain_is_peeled_in_order() {
    elab(
        r#"
        record Slot(n: Nat) { at: Nat, }
        record Spec(level: Nat, n: Nat, slot: Slot(n), value: Nat) {
            at_level: level = level,
            picked: slot.at = slot.at,
        }

        fn Consumer(rel: (n: Nat) -> Slot(n) -> Nat -> Type) -> Type {
            (n: Nat) -> (p: Slot(n)) -> (v: Nat) -> rel(n, p, v)
        }

        fn SpecSpelled(level: Nat, n: Nat, slot: Slot(n), value: Nat) -> Type {
            Spec(level, n, slot, value)
        }

        theorem certified(level: Nat): Consumer(Spec(level))
        { λ n p v => Spec { at_level: refl, picked: refl } }

        theorem wrapped(level: Nat): Consumer(SpecSpelled(level))
        { λ n p v => Spec { at_level: refl, picked: refl } }

        theorem agree(level: Nat): Consumer(Spec(level)) { wrapped(level) }
        "#,
    );
}

// The relation slot the showcase actually writes is a **record's** value
// parameter, not a `fn`'s (`Certified<Char, Expr>(source, begin,
// GrammarSpec(level))`), so the checking position is `valparam_args`. Same arm,
// one road over, and the field that consumes the relation is projected out.
#[test]
fn a_records_own_relation_slot_takes_one() {
    elab(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }

        record Certified(rel: Nat -> Type) {
            value: Nat,
            evidence: rel(value),
        }

        fn certified_at(level: Nat) -> Type { Certified(Grammar(level)) }

        fn one(level: Nat) -> Certified(Grammar(level)) {
            Certified { value: 1, evidence: Grammar { at_level: refl } }
        }
        theorem projected(level: Nat): one(level).value = 1 { refl }
        theorem evidence_level(level: Nat): one(level).evidence.at_level = refl { refl }
        "#,
    );
}

// The **open element type** axis, the one that hid three of the five defects
// `docs/testing-generated-terms.md` counts. `Boxed<A>` is monomorphized, so
// `Boxed` is no `Type -> Type` value — but `Boxed<A>(v)` with `A` the
// enclosing declaration's own parameter is a `Nat -> Type` value, and the
// partial application is written through the explicit type application.
#[test]
fn an_open_element_type_comes_along() {
    elab(
        r#"
        record Boxed<A>(v: Nat, w: Nat) { val: A, pf: v = v, qf: w = w, }

        fn Fam(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) }

        // open: `A` is this declaration's parameter
        fn OpenFam<A>(v: Nat) -> Type { Fam(Boxed<A>(v)) }

        // a closed instantiation of the same declaration, inhabited and used
        fn at_nat() -> Fam(Boxed<Nat>(3)) { λ n => Boxed { val: 7, pf: refl, qf: refl } }
        theorem projected(): at_nat()(3).val = 7 { refl }
        theorem open_matches(): OpenFam<Nat>(3) { at_nat() }
        "#,
    );
}

// **The negative control**: the constructor reading of the very same record, in
// the same file. `Two(1)` at `Nat -> Two(n, m)` is the constructor with its
// second *field* abstracted (docs/constructor-function-values.md §2) — the
// expected spine does not end in a universe, so this arm declines and the
// constructor arm below it takes over, exactly as before this round.
#[test]
fn the_constructor_reading_still_wins_below_a_record_codomain() {
    elab(
        r#"
        record Two(n: Nat, m: Nat) { a: Nat, b: Nat, }

        fn Fam(dom: Nat -> Type) -> Type { (k: Nat) -> dom(k) }

        // the type-former reading: one value parameter written, one abstracted
        fn TwoFam(n: Nat) -> Type { Fam(Two(n)) }
        theorem inhabited(n: Nat): Fam(Two(n)) { λ k => Two { a: 1, b: 2 } }

        // the constructor reading, same name, same file: `Two(1)` fills field
        // `a` and η-expands over field `b`
        fn ctor_reading(n: Nat, m: Nat) -> Nat -> Two(n, m) { Two(1) }
        theorem fields(n: Nat, m: Nat): ctor_reading(n, m)(7).b = 7 { refl }
        theorem first_field(n: Nat, m: Nat): ctor_reading(n, m)(7).a = 1 { refl }
        "#,
    );
}

// The diagnostics. The arity mismatch is measured against the **value-parameter
// telescope** and the arrows the expected type supplies, which is the whole
// reason this arm commits once it has seen a universe at the end of the spine
// instead of falling through to the constructor's field count.
#[test]
fn rejections() {
    // Too few arrows: `Grammar` needs two, the relation offers one.
    let msg = elab_err(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }
        fn Fam(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) }
        fn Bad() -> Type { Fam(Grammar) }
        "#,
    );
    assert!(
        msg.contains("needs 2 more value argument(s) to be a type"),
        "{msg}"
    );
    assert!(msg.contains("provides 1 before its `Type`"), "{msg}");
    assert!(!msg.contains("is a constructor of"), "{msg}");

    // Too many arrows: one value parameter left, three arrows offered.
    let msg = elab_err(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }
        fn Fam3(dom: Nat -> Nat -> Nat -> Type) -> Type { (n: Nat) -> dom(n, n, n) }
        fn Bad() -> Type { Fam3(Grammar(0)) }
        "#,
    );
    assert!(
        msg.contains("needs 1 more value argument(s) to be a type"),
        "{msg}"
    );
    assert!(msg.contains("provides 3 before its `Type`"), "{msg}");

    // Non-cumulativity, unchanged: the record lands at level 0 and no lift
    // carries it to `Type<1>` (docs/surface-universe.md §6).
    let msg = elab_err(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }
        fn Fam1(dom: Nat -> Type<1>) -> Type<1> { (n: Nat) -> dom(n) }
        fn Bad() -> Type<1> { Fam1(Grammar(0)) }
        "#,
    );
    assert!(msg.contains("non-cumulative"), "{msg}");

    // The boundary the constructor round drew stays drawn: **inference**
    // position selects no reading, so an unsaturated record name there is
    // still an error.
    let msg = elab_err(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }
        fn Bad() -> Nat { let r = Grammar(0); 0 }
        "#,
    );
    assert!(!msg.is_empty(), "{msg}");
}

// A local binder of the declaration's name keeps its ordinary meaning: the arm
// consults `shadowed` before it consults the registry, so a `Nat -> Nat ->
// Type` *parameter* called `Grammar` is passed along, not lowered. The witness
// distinguishes the two readings — `refl` inhabits the parameter's answer and
// could not inhabit the record's.
#[test]
fn a_shadowing_binder_is_still_the_binder() {
    elab(
        r#"
        record Grammar(level: Nat, value: Nat) { at_level: level = level, }

        fn takes_relation(rel: Nat -> Nat -> Type) -> Type { rel(0, 1) }
        fn Under(Grammar: Nat -> Nat -> Type) -> Type { takes_relation(Grammar) }

        theorem param_wins(): Under(λ (a: Nat) (b: Nat) => a = a) { refl }
        "#,
    );
}
