//! `heather check --expectations`: refusals written as Heather files, next
//! to the theorems they control (`docs/test-value-audit.md` §4.3,
//! `issues/hthr-test-corpus.md`).
//!
//! A declaration is expected to check unless a directive comment directly
//! above it says it is refused, and why:
//!
//! ```heather
//! // expect-error: already has an instance
//! instance Monoid<Bool>(Bool::or) { … }
//!
//! // expect-error(mismatch)
//! theorem wrong(): Bool::Monoid(Bool::or).unit = True { refl }
//! ```
//!
//! The reason is one of
//!
//! - `: <fragment>`: the error's text contains the fragment;
//! - `(kernel)`: the kernel rejected the elaborated declaration;
//! - `(mismatch)`: a checking mismatch (`… is expected here`), what a lemma
//!   cited at the wrong statement or a wrong literal is refused with;
//!
//! or a kind and a fragment together, `(kernel): NotConvertible`. Several
//! directive lines above one declaration must all hold of its error. A bare
//! `// expect-error` is itself an error: a refusal names its reason
//! (`docs/test-value-audit.md` §5). The vocabulary is the Rust tests'
//! `support::assert_refused`, and so is its guard against incidental slips:
//! an error whose headline is an unbound name, a missing module or an
//! ambiguity satisfies a directive only when a fragment asks for it by name,
//! so a typo cannot pass for the refusal it was meant to pin.
//!
//! The checker already keeps going after a refused declaration (a refused
//! item registers nothing, and the next one is checked against the same Ψ),
//! so a corpus file is one ordinary check. Each error is attributed to the
//! declaration whose span holds the error's span. A declaration is refused
//! at most once, so a second error inside one declaration, or one outside
//! every declaration, is never taken as the answer to a directive: it is
//! reported as it stands.
//!
//! Plain `heather check` does not read directives, so a refusal file fails
//! it, and says why: an unflagged check keeps meaning "every declaration
//! checks", as it does beside `--cache`.

use heather_elab::ElabError;
use heather_syntax::Span;

/// Why a directive says its declaration is refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Kernel,
    Mismatch,
}

/// One `// expect-error…` line.
#[derive(Debug, Clone)]
struct Directive {
    kind: Option<Kind>,
    fragment: Option<String>,
}

impl Directive {
    /// The directive as written after `expect-error`, for messages.
    fn spelled(&self) -> String {
        let kind = match self.kind {
            Some(Kind::Kernel) => "(kernel)",
            Some(Kind::Mismatch) => "(mismatch)",
            None => "",
        };
        match &self.fragment {
            Some(f) => format!("expect-error{kind}: {f}"),
            None => format!("expect-error{kind}"),
        }
    }

    /// Whether `err`, rendered against the module's source, is the refusal
    /// this directive describes. `slip_named` says whether some directive on
    /// the same declaration asks for an incidental slip by name.
    fn holds(&self, err: &ElabError, rendered: &str, incidental: bool, slip_named: bool) -> bool {
        if incidental && !slip_named {
            return false;
        }
        let kind = match self.kind {
            None => true,
            Some(Kind::Kernel) => matches!(err, ElabError::Kernel { .. }),
            Some(Kind::Mismatch) => rendered.contains("is expected here"),
        };
        kind && self.fragment.as_ref().is_none_or(|f| rendered.contains(f.as_str()))
    }
}

/// Headlines a slip produces rather than a refusal: the same list as the
/// Rust tests' `support::assert_refused`.
const SLIPS: &[&str] = &["unbound name", "cannot find module", "neither an imported module", "is ambiguous"];
/// Words a fragment uses when it means to pin one of those.
const SLIP_WORDS: &[&str] = &["unbound", "module", "ambiguous", "parse"];

/// The outcome of a module's check, read against its directives.
pub struct Verdict {
    /// What is still an error: refusals nothing expected, directives not met,
    /// and misplaced or reasonless directives.
    pub errors: Vec<ElabError>,
    /// Declarations refused exactly as their directives said.
    pub matched: usize,
}

/// How many directive lines `src` holds, for the hint plain `check` prints
/// beside a refusal file's errors.
pub fn count(src: &str) -> usize {
    directive_lines(src).count()
}

/// Read `errors`, the diagnostics of checking the module `src`, against the
/// directives in `src`.
pub fn judge(src: &str, errors: Vec<ElabError>) -> Verdict {
    if count(src) == 0 {
        return Verdict { errors, matched: 0 };
    }
    // The checker parsed this source a moment ago; a parse error is already
    // among `errors`, and with no items there is nothing to attribute.
    let Ok(file) = heather_syntax::parse_file(src) else {
        return Verdict { errors, matched: 0 };
    };
    let items: Vec<Span> = file.items.iter().map(|i| i.span()).collect();
    let mut out = Vec::new();
    // Directives grouped by the declaration below them.
    let mut expected: Vec<(usize, Vec<Directive>)> = Vec::new();
    for (span, body) in directive_lines(src) {
        let directive = match parse(body) {
            Ok(d) => d,
            Err(msg) => {
                out.push(ElabError::Elab { msg, span });
                continue;
            }
        };
        match placement(src, &items, span) {
            Ok(idx) => match expected.iter_mut().find(|(i, _)| *i == idx) {
                Some((_, ds)) => ds.push(directive),
                None => expected.push((idx, vec![directive])),
            },
            Err(msg) => out.push(ElabError::Elab { msg, span }),
        }
    }
    // Each error goes to the declaration that holds it, or stays loose.
    let mut owned: Vec<Vec<ElabError>> = vec![Vec::new(); items.len()];
    for err in errors {
        let at = err.span().and_then(|s| items.iter().position(|i| i.start <= s.start && s.start < i.end));
        match at {
            Some(idx) if expected.iter().any(|(i, _)| *i == idx) => owned[idx].push(err),
            _ => out.push(err),
        }
    }
    let mut matched = 0;
    for (idx, directives) in &expected {
        let mut errs = std::mem::take(&mut owned[*idx]);
        let wanted = directives.iter().map(Directive::spelled).collect::<Vec<_>>().join("`, `");
        match errs.len() {
            0 => out.push(ElabError::Elab {
                msg: format!("this declaration checks, but `{wanted}` says it is refused"),
                span: items[*idx],
            }),
            1 => {
                let err = errs.pop().expect("one error");
                let rendered = err.render(src);
                let headline = rendered.lines().find(|l| !l.trim().is_empty()).unwrap_or("");
                let incidental = matches!(err, ElabError::Parse(_)) || SLIPS.iter().any(|s| headline.contains(s));
                let slip_named = directives
                    .iter()
                    .any(|d| d.fragment.as_ref().is_some_and(|f| SLIP_WORDS.iter().any(|w| f.contains(w))));
                if directives.iter().all(|d| d.holds(&err, &rendered, incidental, slip_named)) {
                    matched += 1;
                } else {
                    let span = err.span().unwrap_or(items[*idx]);
                    let why = if incidental && !slip_named {
                        " (an incidental slip satisfies a directive only when a fragment names it)"
                    } else {
                        ""
                    };
                    out.push(ElabError::Elab {
                        msg: format!(
                            "this declaration is refused, but not as `{wanted}` says{why}; the refusal was:\n{rendered}"
                        ),
                        span,
                    });
                }
            }
            // A declaration is refused once; more than one error inside it
            // is not an answer to a directive, so all of them stand.
            _ => out.extend(errs),
        }
    }
    // In source order, as the checker reports them.
    out.sort_by_key(|e| e.span().map_or(usize::MAX, |s| s.start));
    Verdict { errors: out, matched }
}

/// Every `// expect-error…` line: its span and what follows `expect-error`.
/// Doc comments (`///`) are prose and never directives.
fn directive_lines(src: &str) -> impl Iterator<Item = (Span, &str)> {
    let mut offset = 0;
    src.split_inclusive('\n').filter_map(move |line| {
        let start = offset;
        offset += line.len();
        let text = line.trim_end_matches(['\n', '\r']);
        let lead = text.len() - text.trim_start().len();
        let comment = text.trim_start().strip_prefix("//")?;
        if comment.starts_with('/') {
            return None;
        }
        let body = comment.trim_start().strip_prefix("expect-error")?;
        Some((Span { start: start + lead, end: start + text.len() }, body))
    })
}

/// `(kind)`, `: fragment`, or both, after `expect-error`.
fn parse(body: &str) -> Result<Directive, String> {
    let mut rest = body.trim_start();
    let mut kind = None;
    if let Some(after) = rest.strip_prefix('(') {
        let Some((word, tail)) = after.split_once(')') else {
            return Err("an expectation's kind is closed by `)`: `// expect-error(kernel)`".into());
        };
        kind = Some(match word.trim() {
            "kernel" => Kind::Kernel,
            "mismatch" => Kind::Mismatch,
            other => {
                return Err(format!(
                    "`{other}` is not a refusal kind: write `(kernel)`, `(mismatch)`, or `: <what the error says>`"
                ));
            }
        });
        rest = tail.trim_start();
    }
    let fragment = match rest.strip_prefix(':') {
        Some(f) if !f.trim().is_empty() => Some(f.trim().to_string()),
        Some(_) => return Err("`expect-error:` needs the text the error says after the colon".into()),
        None if rest.is_empty() => None,
        None => return Err(format!("unexpected `{rest}` in an expectation: write `// expect-error: <what the error says>`")),
    };
    if kind.is_none() && fragment.is_none() {
        return Err(
            "an expectation names its reason: `// expect-error: <what the error says>`, `(kernel)` or `(mismatch)`".into(),
        );
    }
    Ok(Directive { kind, fragment })
}

/// The declaration a directive at `line` belongs to: the next one, with only
/// comments and blank lines between them.
fn placement(src: &str, items: &[Span], line: Span) -> Result<usize, String> {
    if items.iter().any(|i| i.start <= line.start && line.start < i.end) {
        return Err("an expectation goes above a declaration (and its doc comment), not inside it".into());
    }
    let Some(idx) = items.iter().position(|i| i.start >= line.end) else {
        return Err("no declaration follows this expectation".into());
    };
    let between = &src[line.end..items[idx].start];
    if between.lines().all(|l| l.trim().is_empty() || l.trim_start().starts_with("//")) {
        Ok(idx)
    } else {
        Err("an expectation sits directly above the declaration it describes".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn directives_are_read_with_their_reasons() {
        let src = "// expect-error: no instance\nfn f() -> Nat { 0 }\n/// expect-error: prose\n  // expect-error(kernel)\n";
        let lines: Vec<&str> = directive_lines(src).map(|(_, b)| b).collect();
        assert_eq!(lines, [": no instance", "(kernel)"]);
        let d = parse(": no instance").expect("fragment");
        assert_eq!((d.kind, d.fragment.as_deref()), (None, Some("no instance")));
        let d = parse("(mismatch)").expect("kind");
        assert_eq!((d.kind, d.fragment), (Some(Kind::Mismatch), None));
        let d = parse("(kernel): NotConvertible").expect("both");
        assert_eq!((d.kind, d.fragment.as_deref()), (Some(Kind::Kernel), Some("NotConvertible")));
    }

    #[test]
    fn a_directive_without_a_reason_is_refused() {
        assert!(parse("").unwrap_err().contains("names its reason"));
        assert!(parse(":  ").unwrap_err().contains("after the colon"));
        assert!(parse("(typo)").unwrap_err().contains("not a refusal kind"));
        assert!(parse("(kernel").unwrap_err().contains("closed by"));
        assert!(parse(" says nothing").unwrap_err().contains("unexpected"));
    }
}
