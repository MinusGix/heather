---
title: "Syntax-highlight source excerpts in terminal diagnostics"
status: open
labels: [tooling,cli,diagnostics,syntax,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

Heather's terminal diagnostics now distinguish their structure with ANSI
color: severity, location, gutter, caret, summary, and successful result. The
quoted source line deliberately remains plain. Give that excerpt modest syntax
highlighting so a dense dependent type or match motive is easier to scan,
without turning diagnostic rendering into a second editor frontend.

The likely first implementation should use `heather-syntax`'s lexer, which the
CLI already depends on. Token spans are enough to color keywords, numerals,
operators, punctuation, and a few lexically certain name forms on the one
rendered source line. It would share Heather's actual token vocabulary, add no
dependency, and preserve the diagnostic renderer's already-computed columns
because escape sequences are inserted only after layout.

Tree-sitter is a viable but heavier alternative. `tree-sitter-heather` already
has a Rust binding and a highlight query, so the CLI could parse the module and
apply those captures. Doing that well would bring the Tree-sitter runtime (and
possibly highlight-query machinery) into the deliberately dependency-light
main workspace, connect it to a grammar currently packaged as a standalone
nested workspace, and maintain a second parse for excerpts whose source AST
Heather has already parsed. Incremental parsing offers little for a one-shot
CLI. Prefer this route only if a lexer spike shows that the editor query's
extra classifications materially improve real diagnostics or if a shared
highlight service gains another non-editor customer.

This is intentionally presentation-only. It must not use elaborated names to
rewrite source, infer semantics from identifier casing, or alter span/caret
calculation.

## Acceptance

- Source excerpts color lexically certain categories with a restrained palette
  that remains readable alongside yellow warnings and red errors.
- The renderer consumes Heather lexer spans rather than maintaining a second
  handwritten keyword/operator list.
- Plain output remains byte-for-byte unchanged when the stream is redirected,
  `NO_COLOR` is present, or `TERM=dumb`.
- ANSI escapes are inserted after line, column, and caret widths are computed;
  Unicode source and tabs retain their current alignment behavior.
- Lexing failure or an unusual partial token degrades to an uncolored excerpt,
  never a lost diagnostic or CLI failure.
- Tests pin representative keywords, operators, numerals, comments, Unicode
  syntax, a plain-output control, and a caret-alignment control.

## What it assumes from elsewhere

- **[[tree-sitter-zed-language-support]]** owns the editor grammar and highlight
  query. This issue may consume them if the Tree-sitter route wins, but does
  not duplicate or redefine their syntax inventory.
- **[[diagnostics-name-the-written-form]]** owns preserving the source spelling
  named by a diagnostic. This issue colors the excerpt it receives and makes
  no naming decision.

## Log

- 2026-08-22: Filed with automatic terminal color as the baseline. Initial
  recommendation is lexer-span highlighting: the CLI already has the exact
  lexer, while embedding Tree-sitter would be reasonable but disproportionate
  until the extra editor-grade classifications have a demonstrated payoff.
