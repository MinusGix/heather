---
title: Diagnostics inside a desugared or generated match name the wrong form and site
status: open
labels: [frontend,diagnostics]
created: 2026-08-05
updated: 2026-08-09
---



Two rounds have now shipped a desugaring whose diagnostics name the form the
*elaborator* sees rather than the one the user wrote. Neither is misleading —
the constructor names and the arm in question are always correct — but both
point somewhere the user did not type.

1. **`split` says `match`** (`docs/match-equation-split-design.md` §6). Five
   message sites in `inductive.rs` / `elab_match_nat` say "`match` is missing
   an arm for `C`" at a block whose text says `split`/`on`.
2. **A non-exhaustive *inner* column of a deep pattern reports at the outer
   `match`** (`docs/nested-match-patterns-design.md` §3.4). The generated
   inner `match` carries the whole match's span, because there is no source
   text for the level it is reporting about — the user wrote a *pattern*, and
   the missing constructor belongs to a column, not to an arm. Pinned by
   `a_deep_match_with_no_fallthrough_is_not_exhaustive` in
   `crates/elab/tests/nested_match_patterns.rs`, so an improvement has to
   change a test deliberately.

The shape of a fix is the same for both: thread a *site* — a form name and a
span — into the five message sites, set by whoever built the arms. It was
declined twice for the same reason (five messages and their tests for a
cosmetic gain), which is the argument for giving it one owner rather than
re-deciding it every round.

## What it assumes from elsewhere

- **[[match-with-equation]]** / **[[split-on-arms]]** and
  **[[nested-match-patterns]]** own their desugarings. Assumed here: only that both build
  `ExprKind::Match` nodes the elaborator cannot distinguish from written ones,
  which is the property that makes the messages wrong and is also the property
  that made both rounds cheap.

## Log

- 2026-08-09: Partial payment from the operators round: operator applications now render as written (a + b, not add(a)(b)) via render_expr's re-sugaring.
