//! The formatter's invariants, and the rules it is sure about.
//!
//! Two categories, kept visibly apart because they are guaranteed differently.
//! *Safety* is mechanical: the token stream and the line structure must survive
//! formatting, checked over the whole repository corpus, and that is what makes
//! a whole-library reformat something anyone can approve. *Taste* is not
//! mechanical — `⟨a |⟩` and `⟨a | ⟩` lex identically — so each spacing rule
//! needs a case that says what it should look like.

use heather_syntax::fmt::format_source;
use heather_syntax::lexer::{lex, TokKind};
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn corpus() -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|x| x == "hthr") {
                out.push(p);
            }
        }
    }
    let root = repo_root();
    let mut files = Vec::new();
    walk(&root.join("lib"), &mut files);
    walk(&root.join("examples"), &mut files);
    walk(&root.join("crates"), &mut files);
    files.sort();
    assert!(!files.is_empty(), "no .hthr corpus found");
    files
}

fn kinds(src: &str) -> Vec<TokKind> {
    lex(src).expect("lexes").into_iter().map(|t| t.kind).collect()
}

/// For each adjacent token pair, whether a line break separates them. This is
/// the precise content of "the formatter moves no line break": collapsing a run
/// of blank lines changes line *numbers*, but may never change which tokens
/// share a line.
fn line_splits(src: &str) -> Vec<bool> {
    let toks = lex(src).expect("lexes");
    toks.windows(2)
        .map(|w| src[w[0].span.end..w[1].span.start].contains('\n'))
        .collect()
}

#[test]
fn formatting_preserves_the_token_stream() {
    for path in corpus() {
        let src = std::fs::read_to_string(&path).unwrap();
        let out = format_source(&src);
        assert_eq!(
            kinds(&out),
            kinds(&src),
            "{}: formatting changed the token stream",
            path.display()
        );
    }
}

#[test]
fn formatting_moves_no_line_break() {
    for path in corpus() {
        let src = std::fs::read_to_string(&path).unwrap();
        let out = format_source(&src);
        assert_eq!(
            line_splits(&out),
            line_splits(&src),
            "{}: formatting moved a line break",
            path.display()
        );
    }
}

#[test]
fn formatting_is_idempotent() {
    for path in corpus() {
        let src = std::fs::read_to_string(&path).unwrap();
        let once = format_source(&src);
        assert_eq!(format_source(&once), once, "{}: formatting is not stable", path.display());
    }
}

/// The reformat must be invisible to `git diff -w`, which is what makes a
/// 22k-line mechanical rewrite reviewable.
#[test]
fn formatting_changes_only_whitespace() {
    fn squeeze(s: &str) -> String {
        s.chars().filter(|c| !c.is_whitespace()).collect()
    }
    for path in corpus() {
        let src = std::fs::read_to_string(&path).unwrap();
        assert_eq!(
            squeeze(&format_source(&src)),
            squeeze(&src),
            "{}: formatting changed more than whitespace",
            path.display()
        );
    }
}

fn check(input: &str, want: &str) {
    let got = format_source(input);
    assert_eq!(got.trim_end(), want, "input: {input:?}");
    assert_eq!(kinds(&got), kinds(input), "token stream changed: {input:?}");
}

#[test]
fn argument_lists_close_up_and_commas_open_up() {
    check(
        "fn map_at<T,A,B>(source: List<T>,begin: Cursor<T>) -> Reply<T,B> { f(a,b) }",
        "fn map_at<T, A, B>(source: List<T>, begin: Cursor<T>) -> Reply<T, B> { f(a, b) }",
    );
    check("fn f() -> Nat { g( x , y ) }", "fn f() -> Nat { g(x, y) }");
}

/// `<` is padded as a comparison and hugged as a delimiter, in one line.
#[test]
fn the_two_roles_of_angle_brackets() {
    check(
        "theorem t<A>(n: Nat, xs: List<A>): n<succ(n) { p }",
        "theorem t<A>(n: Nat, xs: List<A>): n < succ(n) { p }",
    );
}

/// `Pos<A>` is parser sugar whose AST keeps only the carrier, so its list is
/// found from the tokens around the carrier: a parameter run, a nested
/// carrier, and a function result, each beside a real comparison.
#[test]
fn pos_sugar_angle_brackets_are_delimiters() {
    check(
        "theorem t(a,b: Pos<Nat>,xs: Pos<List<Nat> >): 0<a { a_pos }",
        "theorem t(a, b: Pos<Nat>, xs: Pos<List<Nat>>): 0 < a { a_pos }",
    );
    check("fn ten(i: Nat) -> Pos<Nat> { 10 }", "fn ten(i: Nat) -> Pos<Nat> { 10 }");
}

#[test]
fn projections_and_qualified_names_stay_tight() {
    check("fn f(p: Pair) -> Nat { p . fst }", "fn f(p: Pair) -> Nat { p.fst }");
    check("import nat::{le_refl, le_trans};", "import nat::{le_refl, le_trans};");
}

/// Inherited from the `tight-negation-spacing` lint, which this replaces.
#[test]
fn prefix_negation_is_written_tight() {
    check("theorem t(P: Type): ¬ P { p }", "theorem t(P: Type): ¬P { p }");
    check("fn f(b: Bool) -> Bool { ! b }", "fn f(b: Bool) -> Bool { !b }");
}

#[test]
fn boolean_reflection_delimiters_are_written_tight() {
    check("theorem t(b: Bool): ⟦ b ⟧ { p }", "theorem t(b: Bool): ⟦b⟧ { p }");
    check(
        "theorem t(a, b: Bool): ⟦ ! a && b ⟧ { p }",
        "theorem t(a, b: Bool): ⟦!a && b⟧ { p }",
    );
}

/// The other half of that lint: a comment between operator and operand is not
/// whitespace, and closing the gap would swallow it.
#[test]
fn a_comment_after_a_prefix_operator_survives() {
    let src = "theorem t(P: Type): ¬ // why\n    P { p }\n";
    assert_eq!(format_source(src), src);
}

/// `?p` is the named hole and `? p` is an anonymous hole applied to `p`. The
/// lexer decides this by adjacency, so closing or opening that gap would change
/// the program — the one hazard the token-stream check exists to catch.
#[test]
fn hole_adjacency_is_never_edited() {
    for src in ["fn f() -> Nat { g(?p) }\n", "fn f() -> Nat { g(? p) }\n"] {
        assert_eq!(format_source(src), src, "edited a hole's adjacency");
    }
}

/// Anonymous-constructor injections lex the same spaced or tight, so the
/// formatter must not have an opinion it cannot justify.
#[test]
fn anonymous_constructor_injections_are_left_alone() {
    for src in ["fn f() -> T { ⟨a |⟩ }\n", "fn f() -> T { ⟨| b⟩ }\n", "fn f() -> T { ⟨a, b⟩ }\n"] {
        assert_eq!(format_source(src), src);
    }
}

/// Formatting is for source that does not compile, too.
#[test]
fn an_unparseable_file_is_still_formatted() {
    let out = format_source("fn f(a,b) -> { this is not heather");
    assert!(out.contains("f(a, b)"), "commas went unformatted: {out:?}");
}

/// With no parse there is no role for `<`, so it is left exactly as written
/// rather than guessed at in either direction.
#[test]
fn angle_brackets_are_left_alone_without_a_parse() {
    // The commas are still normalized; only the `<`/`>` spacing is deferred,
    // and it is deferred in *both* directions — neither closed up nor padded.
    for (src, want) in [
        ("fn f(x: Vec<T,A>) -> { ???\n", "fn f(x: Vec<T, A>) -> { ???"),
        ("fn f(x: Vec< T , A >) -> { ???\n", "fn f(x: Vec< T, A >) -> { ???"),
    ] {
        let out = format_source(src);
        assert_eq!(kinds(&out), kinds(src));
        assert_eq!(out.trim_end(), want, "guessed at `<`: {out:?}");
    }
}

#[test]
fn trailing_blanks_go_and_one_final_newline_stays() {
    assert_eq!(format_source("fn f() -> Nat { 0 }   \n\n\n\n"), "fn f() -> Nat { 0 }\n");
    assert_eq!(format_source("fn f() -> Nat { 0 }"), "fn f() -> Nat { 0 }\n");
}

#[test]
fn at_most_one_blank_line_between_items() {
    let src = "fn a() -> Nat { 0 }\n\n\n\n\nfn b() -> Nat { 1 }\n";
    assert_eq!(format_source(src), "fn a() -> Nat { 0 }\n\nfn b() -> Nat { 1 }\n");
}

/// A declared operator symbol has no operand to hug: `designation prefix - at
/// Int := neg` must not become `-at`. Both spellings lex identically, so no
/// invariant catches this — only the rule knowing what the `-` is doing.
#[test]
fn a_declared_operator_symbol_is_not_a_prefix_operator() {
    for src in [
        "designation prefix - at Int := neg\n",
        "designation prefix ! at Bool := not\n",
        "designation<A> ++ at List<A> := append\n",
        "designation < at Int := lt\n",
    ] {
        assert_eq!(format_source(src), src, "restyled a declared symbol");
    }
}

/// The gate: the repository's own Heather source is already formatted.
///
/// A Rust test rather than a step in `scripts/test`, so the ordinary suite
/// enforces this without building the CLI in release. `scripts/fmt` is the
/// fixing half.
#[test]
fn repository_sources_are_formatted() {
    let root = repo_root();
    let unformatted: Vec<String> = corpus()
        .into_iter()
        .filter(|p| {
            let src = std::fs::read_to_string(p).unwrap();
            format_source(&src) != src
        })
        .map(|p| p.strip_prefix(&root).unwrap_or(&p).display().to_string())
        .collect();
    assert!(
        unformatted.is_empty(),
        "these files are not formatted; run `scripts/fmt`:\n  {}",
        unformatted.join("\n  ")
    );
}
