---
title: "Lint whitespace after prefix negation"
status: closed
labels: [tooling,lint,syntax,stdlib,ergonomics]
created: 2026-08-20
updated: 2026-09-16
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
- 2026-08-22: Implemented as the default `tight-negation-spacing` lint over a
  shared once-per-file token view. It reports only whitespace trivia, leaves a
  comment between the operator and operand alone, and carries the exact empty
  replacement as structured fix data. The stdlib's two remaining occurrences
  were normalized and the focused warning tests cover both the fix and comment
  control.
- 2026-09-16: Whitespace may acquire a different owner: [[heather-formatter]] proposes a token-stream formatter that would make this rule mechanical rather than advisory. Decide there whether this lint is subsumed or is the story for people who do not run it.
