---
title: "Lint explicit match motives that ordinary synthesis can recover"
status: open
labels: [tooling,lint,frontend,elaboration,ergonomics]
created: 2026-08-22
updated: 2026-08-22
---

An explicit `match e as λ x => P(x)` motive is often historical inference
debt rather than information Heather still needs. Warn only when the existing
goal-derived motive synthesis can recover an equivalent motive and the same
match checks without the written annotation.

This must be an elaboration-backed lint, not a surface-shape rule. Comparing
the written motive with a synthesized candidate may be sufficient if all arm
checking inputs are thereby identical; otherwise validate omission in an
isolated speculative item check. Speculation must not leak metavariables,
goals, warnings, instances, declarations, or fuel state into the real check.

An explicit motive can also be valuable documentation. Until Heather has
per-site suppression, the default recognizer should limit itself to motives
whose omission is both mechanically verified and clearly no more informative
than the inferred goal. A stricter stdlib profile can adopt broader canonical
surface policy after the audit.

## Acceptance

- The lint proves that omission checks; it never infers redundancy from motive
  shape or from a similar neighboring declaration.
- Dependent motives, nested matches, checking versus inference position,
  convoyed hypotheses, and field-binder abstraction have positive and negative
  controls.
- Speculation is transactionally silent and does not duplicate expensive
  kernel gates on declarations that cannot possibly qualify.
- The diagnostic offers the exact motive-free spelling and retains an explicit
  motive when it is required or materially documents an otherwise hidden
  dependency.
- The census in [[match-motive-surface-audit]] is rerun with verified buckets.

## What it assumes from elsewhere

- [[lint-roadmap]] owns rollout policy.
- [[match-motive-surface-audit]] owns the full motive census and any replacement
  syntax for motives that remain genuinely necessary.

## Log

- 2026-08-22: Filed as the semantic counterpart to
  [[lint-match-function-application]]: that rule recognizes one rewrite shape;
  this rule asks the elaborator whether the motive itself is actually needed.
