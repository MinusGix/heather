---
title: "Lint whitespace after prefix negation"
status: open
labels: [tooling,lint,syntax,stdlib,ergonomics]
created: 2026-08-20
updated: 2026-08-20
---

The standard style is tight prefix notation: `¬P` and `¬(a = b)`, not
`¬ P` or `¬ (a = b)`. Add a source-aware lint so new library code does not
drift back after the manual cleanup.

This is a written-form rule. The parser erases whitespace and elaboration sees
the same negation application either way, so the lint must inspect token/span
provenance rather than the elaborated term. It should offer a mechanical fix
that removes only the trivia between `¬` and its operand.

## Acceptance

- The lint flags whitespace between prefix `¬` and either an atom or a
  parenthesized operand.
- `¬P`, `¬(P)`, nested negations, comments, and string contents are handled
  without false positives.
- The diagnostic shows the preferred spelling and has an exact safe fix.
- `lib/std` enables the rule in its ordinary lint/test workflow.

## What it assumes from elsewhere

- [[stdlib-surface-style-lint]] owns the common source-provenance machinery and
  rollout policy; this issue is the bounded spacing rule.

## Log

- 2026-08-20: Filed after the standard library was normalized to tight `¬`.
