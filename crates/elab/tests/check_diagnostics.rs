//! `check_source` and the diagnostic renderings behind `heather check`
//! (issues/cli-check-diagnostics.md): per-declaration recovery, the span on
//! a kernel rejection, and the caret snippets.

use heather_elab::{ElabError, Elaborator};

fn check(src: &str) -> Vec<ElabError> {
    Elaborator::with_prelude().expect("prelude").check_source(src)
}

#[test]
fn clean_file_reports_nothing() {
    let errs = check(
        "theorem succ_cong2({a: Nat}, {b: Nat}, p: a = b): Succ(Succ(a)) = Succ(Succ(b)) {\n\
             cong_succ(cong_succ(p))\n\
         }\n",
    );
    assert!(errs.is_empty(), "expected no diagnostics, got {errs:?}");
}

#[test]
fn recovery_reports_every_bad_declaration_and_checks_the_good_ones() {
    // Declaration 2 is a kernel rejection and 4 has an open goal; 1 and 3
    // are fine, and 3 *uses* 1 — so recovery must leave a successful
    // declaration registered while an intervening failure registers nothing.
    let src = "fn id_nat(n: Nat) -> Nat {\n\
                   n\n\
               }\n\
               theorem broken(n: Nat): n = Succ(n) {\n\
                   refl\n\
               }\n\
               theorem uses_id(n: Nat): id_nat(n) = n {\n\
                   refl\n\
               }\n\
               theorem open_goal(n: Nat): n = n {\n\
                   ?later\n\
               }\n";
    let errs = check(src);
    assert_eq!(errs.len(), 2, "expected exactly the two bad declarations: {errs:?}");
    assert!(
        matches!(&errs[0], ElabError::Kernel { decl, .. } if decl == "broken"),
        "first should be the kernel rejection of `broken`: {:?}",
        errs[0]
    );
    assert!(
        matches!(&errs[1], ElabError::UnsolvedGoals { decl, .. } if decl == "open_goal"),
        "second should be the goal listing of `open_goal`: {:?}",
        errs[1]
    );
}

#[test]
fn failed_declaration_registers_nothing() {
    // `broken` fails, so a later use of it is an ordinary unbound-name
    // error rather than a use of half-registered state.
    let src = "theorem broken(n: Nat): n = Succ(n) {\n\
                   refl\n\
               }\n\
               theorem wants_broken(n: Nat): Succ(n) = Succ(Succ(n)) {\n\
                   cong_succ(broken(n))\n\
               }\n";
    let errs = check(src);
    assert_eq!(errs.len(), 2, "{errs:?}");
    let second = errs[1].to_string();
    assert!(second.contains("broken"), "should name the missing declaration: {second}");
}

#[test]
fn parse_error_is_wholesale() {
    let errs = check("fn f(n: Nat -> Nat { n }\nfn g(n: Nat) -> Nat { n }\n");
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(matches!(errs[0], ElabError::Parse(_)), "{:?}", errs[0]);
}

#[test]
fn kernel_rejection_renders_with_the_declaration_position() {
    let src = "fn id_nat(n: Nat) -> Nat {\n\
                   n\n\
               }\n\
               theorem broken(n: Nat): n = Succ(n) {\n\
                   refl\n\
               }\n";
    let errs = check(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    let rendered = errs[0].render(src);
    assert!(
        rendered.starts_with("4:1:"),
        "a kernel rejection should point at its declaration: {rendered}"
    );
}

#[test]
fn snippet_puts_the_caret_under_the_span() {
    let src = "fn f(n: Nat) -> Nat {\n    missing\n}\n";
    let errs = check(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    let s = errs[0].render_snippet(src, "f.hthr");
    assert!(s.contains("  --> f.hthr:2:5"), "location header: {s}");
    assert!(s.contains("2 |     missing\n"), "quoted source line: {s}");
    assert!(s.contains("  |     ^^^^^^^\n"), "caret run under the span: {s}");
}

#[test]
fn snippet_caret_stays_aligned_past_non_ascii() {
    // The é before the unbound name is two bytes, one column: a byte-counted
    // caret would land one column right of the span.
    let src = "// é\nfn f(n: Nat) -> Nat {\n    missing\n}\n";
    let errs = check(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    let s = errs[0].render_snippet(src, "f.hthr");
    assert!(s.contains("  |     ^^^^^^^\n"), "caret run: {s}");
}

#[test]
fn multi_line_span_carets_only_its_first_line() {
    // The kernel rejection's span is the whole declaration; the caret run
    // must stop at the end of the first line rather than spill.
    let src = "theorem broken(n: Nat): n = Succ(n) {\n    refl\n}\n";
    let errs = check(src);
    let s = errs[0].render_snippet(src, "f.hthr");
    let caret_line = s.lines().last().unwrap();
    let source_line = "theorem broken(n: Nat): n = Succ(n) {";
    assert_eq!(
        caret_line.trim_start_matches([' ', '|']).len(),
        source_line.len(),
        "caret run should cover exactly the first source line: {s}"
    );
}

#[test]
fn goal_listing_renders_with_file_positions() {
    let src = "theorem open_goal(n: Nat): n = n {\n    ?later\n}\n";
    let errs = check(src);
    let s = errs[0].render_snippet(src, "f.hthr");
    assert!(s.contains("unsolved goals in `open_goal`"), "{s}");
    assert!(s.contains("?later"), "{s}");
    assert!(s.contains("(f.hthr:2:5)"), "goal position with filename: {s}");
    assert!(s.contains("discharge each with"), "{s}");
}
