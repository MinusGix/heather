---
title: "A review-only lint tier for optional simplification advice"
status: open
labels: [tooling,lint,diagnostics,design,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

Some observations are valuable during an explicit request for review but are
not evidence that ordinary source has a problem. A removable type annotation
is the motivating example: inference may prove it unnecessary, while the
annotation still communicates intent to a reader.

Add an opt-in **review-only** activation tier. It is orthogonal to style
profiles: `Stdlib` answers which conventions a project adopts, while the tier
answers how eager diagnostics should be. Ordinary `check` remains limited to
high-confidence warnings. A review command, editor action, or future CLI flag
may additionally request advisory findings.

Review-only findings should still use stable `Lint` identities, structured
fixes, ordinary source spans, and the same transactional guarantees. The tier
is not permission for heuristic noise: every finding still needs a useful
explanation and false-positive controls.

Initial candidate customers are removable type annotations,
[[lint-vacuous-match]], proof-style rewrites such as
[[lint-proof-apply]], and any broad form of [[lint-trivial-argument-slot]].

## Acceptance

- Activation level and project/style profile are separate dimensions.
- The ordinary std check output is unchanged when review-only lints exist.
- Callers can request review findings without parsing diagnostic messages or
  constructing a special source path.
- Tests pin default silence, explicit activation, deterministic ordering, and
  the existing failed/generated-declaration suppression.
- The UI wording distinguishes optional advice from an ordinary warning if
  both are rendered together.

## What it assumes from elsewhere

- [[lint-roadmap]] owns the conservative-default policy and lint registry.

## Log

- 2026-08-22: Filed after deciding that mechanically removable annotations
  can be useful review comments without being problems worth showing on every
  check.
