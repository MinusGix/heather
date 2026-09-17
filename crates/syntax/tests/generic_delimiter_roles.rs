//! Is every `>` accounted for? — the premise `crates/syntax/src/roles.rs` rests
//! on (issues/heather-formatter.md).
//!
//! `TokKind::Lt` is emitted for both the comparison operator (`a < b`) and the
//! opener of a type-argument list (`Vec<T, A>`), so the token stream alone
//! cannot say which spacing a `<` wants. `TokKind::Gt` is unambiguous — `>` is
//! never an operator — so every `>` in a file closes exactly one argument list.
//!
//! That gives a completeness check for free: derive one `(open, close)` pair
//! per list from the AST and require the derived closers to be exactly the
//! file's `Gt` tokens. If the two agree over the whole corpus, the derivation
//! found every list and the remaining `Lt` are comparisons.
//!
//! This runs against the shipped derivation, not a copy of it: a new
//! argument-list site added to the grammar without a case in `roles.rs` shows
//! up here as an unaccounted-for `>`.

use heather_syntax::lexer::{lex, TokKind};
use heather_syntax::{argument_lists, parse_file, Delims};
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."))
}

fn hthr_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            hthr_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "hthr") {
            out.push(p);
        }
    }
}

#[test]
fn every_gt_is_accounted_for() {
    let root = repo_root();
    let mut files = Vec::new();
    hthr_files(&root.join("lib"), &mut files);
    hthr_files(&root.join("examples"), &mut files);
    hthr_files(&root.join("crates"), &mut files);
    files.sort();
    assert!(!files.is_empty(), "no .hthr corpus found under {}", root.display());

    let (mut checked, mut unparsed) = (0usize, 0usize);
    let (mut total_gt, mut total_lt, mut opener_lt, mut desugared) = (0usize, 0usize, 0usize, 0usize);
    let mut report = String::new();

    for path in &files {
        let src = std::fs::read_to_string(path).unwrap();
        let Ok(file) = parse_file(&src) else {
            unparsed += 1;
            continue;
        };
        let toks = lex(&src).unwrap();
        let found = argument_lists(&toks, &file);
        let rel = path.strip_prefix(&root).unwrap_or(path).display().to_string();

        // A grouped binder (`before, after: MachineState<Mem>`) gives every name
        // its own `Param` over one written `Ty`, so the same list is reached
        // twice. Identical delimiters are benign; a `<` and a `>` that disagree
        // about their partner would be a real misderivation.
        let mut pairs: Vec<Delims> = found.lists.iter().map(|(_, d)| *d).collect();
        pairs.sort();
        pairs.dedup();
        for a in &pairs {
            let clash = |b: &&Delims| {
                (b.close == a.close && b.open != a.open) || (b.open == a.open && b.close != a.close)
            };
            let rivals: Vec<_> =
                found.lists.iter().filter(|(_, d)| clash(&d)).collect();
            assert!(
                rivals.is_empty(),
                "{rel}: the list {a:?} has a rival claiming one of its delimiters: {rivals:?}"
            );
        }

        let mut gts: Vec<usize> =
            toks.iter().filter(|t| matches!(t.kind, TokKind::Gt)).map(|t| t.span.start).collect();
        gts.sort();
        let mut closes: Vec<usize> = pairs.iter().map(|d| d.close).collect();
        closes.sort();
        if closes != gts {
            let missed: Vec<_> = gts.iter().filter(|g| !closes.contains(g)).take(5).collect();
            let extra: Vec<_> = closes.iter().filter(|c| !gts.contains(c)).take(5).collect();
            report.push_str(&format!(
                "{rel}: {} derived vs {} Gt; missed@{missed:?} extra@{extra:?} undelimited={:?}\n",
                closes.len(),
                gts.len(),
                &found.undelimited[..found.undelimited.len().min(3)],
            ));
        }
        for d in &pairs {
            assert!(
                toks.iter().any(|t| matches!(t.kind, TokKind::Lt) && t.span.start == d.open),
                "{rel}: derived opener at {} is not an `Lt`",
                d.open
            );
        }

        total_gt += gts.len();
        total_lt += toks.iter().filter(|t| matches!(t.kind, TokKind::Lt)).count();
        opener_lt += pairs.len();
        desugared += found.undelimited.len();
        checked += 1;
    }

    eprintln!(
        "census: {checked} files parsed ({unparsed} unparseable, skipped); \
         {total_gt} `>` all accounted for; \
         {total_lt} `<` = {opener_lt} openers + {} comparisons; \
         {desugared} argument lists exist only after desugaring",
        total_lt - opener_lt
    );
    assert!(report.is_empty(), "argument-list derivation disagrees with `>` census:\n{report}");
}
