//! Acceptance for issues/let-else-sugar.md. Positional `if let` is one
//! ordinary pattern row followed by a default row; its optional equation is
//! visible only in the success block and follows `scrutinee = pattern`.

use heather_elab::Elaborator;

const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");

fn with_option() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("option", OPTION).expect("option");
    e
}

fn ok(e: &mut Elaborator, src: &str) {
    e.elab_module_source("probe", src)
        .unwrap_or_else(|err| panic!("{}", err.render(src)));
}

fn bad(e: &mut Elaborator, src: &str) -> String {
    e.elab_module_source("probe", src)
        .expect_err("source must be refused")
        .render(src)
}

#[test]
fn option_computes_in_both_branches_and_matches_the_explicit_form() {
    ok(
        &mut with_option(),
        r#"
        import option;

        fn via_if_let(o: Option<Nat>) -> Nat {
            if let Some(x) = o { x } else { 7 }
        }
        fn via_match(o: Option<Nat>) -> Nat {
            match o { Some(x) => x, _ => 7 }
        }
        theorem some(): via_if_let(Some(4)) = 4 { refl }
        theorem none(): via_if_let(None) = 7 { refl }
        theorem same(o: Option<Nat>): via_if_let(o) = via_match(o) { refl }
        "#,
    );
}

#[test]
fn constant_result_inference_blocks_and_nesting_work() {
    ok(
        &mut with_option(),
        r#"
        import option;

        fn nested(o: Option<Nat>) -> Nat {
            let result: Nat = if let Some(Some(x)) = Some(o) {
                let next = Succ(x);
                next
            } else {
                0
            };
            result
        }
        fn inferred(o: Option<Nat>) -> Nat {
            let result = if let Some(x) = o { x } else { 0 };
            result
        }
        theorem hit(): nested(Some(3)) = 4 { refl }
        theorem inner_miss(): nested(None) = 0 { refl }
        theorem inferred_hit(): inferred(Some(6)) = 6 { refl }
        theorem expression(): (if let Some(x) = Some(5) { x } else { 0 }) = 5 { refl }
        "#,
    );
}

#[test]
fn named_equation_is_scrutinee_to_pattern_and_success_local() {
    ok(
        &mut with_option(),
        r#"
        import option;

        fn consume(o: Option<Nat>, x: Nat, h: o = Some(x)) -> Nat { x }
        fn observed(o: Option<Nat>) -> Nat {
            if let h : Some(x) = o { consume(o, x, h) } else { 0 }
        }
        theorem computes(): observed(Some(9)) = 9 { refl }
        "#,
    );

    let src = r#"
        import option;
        fn bad(o: Option<Nat>) -> Nat {
            if let h : Some(x) = o { x } else { h }
        }
    "#;
    let msg = bad(&mut with_option(), src);
    assert!(msg.contains("unknown name `h`") || msg.contains("unbound"), "{msg}");
}

#[test]
fn irrefutable_default_and_missing_else_have_if_let_diagnostics() {
    let src = r#"
        import option;
        fn bad(o: Option<Nat>) -> Nat { if let _ = o { 1 } else { 0 } }
    "#;
    let msg = bad(&mut with_option(), src);
    assert!(msg.contains("must be refutable"), "{msg}");

    let src = r#"
        import option;
        fn bad(o: Option<Nat>) -> Nat { if let Some(x) = o { x } }
    "#;
    let msg = bad(&mut with_option(), src);
    assert!(msg.contains("`if let` needs an `else"), "{msg}");
}

#[test]
fn indexed_family_keeps_the_existing_homogeneous_equation_boundary() {
    ok(
        &mut with_option(),
        r#"
        inductive MN { MZ, MS(p: MN) }
        inductive VF<A> : (n: MN) -> Type {
            VFNil                              : VF<A>(MZ),
            VFCons(n: MN, x: A, xs: VF<A>(n)) : VF<A>(MS(n)),
        }

        fn empty_tag(n: MN, xs: VF<Nat>(n)) -> MN {
            if let VFNil = xs { MZ } else { MS(MZ) }
        }
        "#,
    );

    let src = r#"
        inductive MN { MZ, MS(p: MN) }
        inductive VF<A> : (n: MN) -> Type {
            VFNil                              : VF<A>(MZ),
            VFCons(n: MN, x: A, xs: VF<A>(n)) : VF<A>(MS(n)),
        }
        fn bad(n: MN, xs: VF<Nat>(n)) -> MN {
            if let h : VFNil = xs { MZ } else { MS(MZ) }
        }
    "#;
    let msg = bad(&mut with_option(), src);
    assert!(msg.contains("indexed family") && msg.contains("inversion"), "{msg}");
}
