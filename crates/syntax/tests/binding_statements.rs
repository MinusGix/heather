//! Parse-level facts of binding statements (docs/sequencing-surface-design.md
//! §3): the lexer's `<-`, and the refusals a whole file's parse owns, which a
//! Heather probe cannot state (a parse error refuses the file). What the
//! lowered forms mean is probed in Heather,
//! `lib/_tests/std/core/binding_statements_tests.hthr`.
use heather_syntax::{parse_file, ExprKind};

fn result_head(src: &str) -> String {
    let file = parse_file(src).unwrap();
    let decl = file.items[0].clone().into_decl();
    match &decl.body.result.kind {
        ExprKind::App { head, .. } => match &head.kind {
            ExprKind::Var(n) => n.clone(),
            other => format!("{other:?}"),
        },
        other => format!("{other:?}"),
    }
}

#[test]
fn binds_lower_to_the_prelude_call_and_leave_no_marker() {
    for src in [
        "fn f(x: M) -> M { let a <- x; g(a) }",
        "fn f(x: M) -> M { let a ← x; g(a) }",
        "fn f(x: M) -> M { let a: Nat <- x; g(a) }",
        "fn f(x: M) -> M { let _ <- x; g(0) }",
        "fn f(x: M) -> M { let { a, b } <- x; g(a) }",
        "fn f(x: M) -> M { x; g(0) }",
        "fn f(x: M) -> M { g(<- x) }",
        "fn f(x: M) -> M { match <- x { A => g(0) } }",
    ] {
        assert_eq!(result_head(src), heather_syntax::BIND_SEQ, "{src}");
        let parsed = format!("{:?}", parse_file(src).unwrap());
        assert!(!parsed.contains("\\0bind"), "{src}");
    }
}

#[test]
fn the_lexer_keeps_iff_and_reads_the_arrow_alone() {
    // `<->` is still the connective, and no bind is read from it.
    let file = parse_file("theorem t(a, b: Type): Type { a <-> b }").unwrap();
    assert!(!format!("{file:?}").contains("Bind::seq"));
}

#[test]
fn a_bind_outside_a_block_or_lambda_body_is_refused() {
    for src in [
        "fn f(x: M) -> F(<- x) { x }",
        "fn f(x: M, y: F(<- x)) -> M { x }",
        "fn f(x: M) -> M { let a <- x; a on _: F(<- x) := x; }",
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains("bind"), "{src}: {}", error.msg);
    }
}

#[test]
fn an_expression_statement_still_needs_a_result_after_it() {
    assert!(parse_file("fn f(x: M) -> M { x; }").is_err());
}
