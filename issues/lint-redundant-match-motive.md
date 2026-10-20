---
title: "Lint explicit match motives that ordinary synthesis can recover"
status: open
labels: [tooling,lint,frontend,elaboration,ergonomics]
area: language
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
- 2026-08-22: Landed the conservative checking-position slice. For each
  explicit non-convoy motive, a cloned elaborator removes it and runs ordinary
  goal-derived checking, then the local kernel checker validates the emitted
  term at the same expected type. The second gate is load-bearing: elaboration
  alone incorrectly nominated three Int lattice proofs, all now pinned as
  retained controls. Diagnostics carry token-completed exact deletions. The
  stdlib adopted 58 verified omissions; this issue stays open for any
  inference-position constant-motive candidates and the broader audit.
- 2026-09-17: 2026-09-17: the probe was the corpus's largest body-elaboration cost, found from [[perf-dashboard]]'s full-corpus reading (decl_body 41% of ir_v1's cold check, 28% of the x86 model's). Every written non-convoy motive in checking position is probed — a clone elaborates the match without it and kernel-checks the result — and a written motive *nested under* a probed one was probed again inside the enclosing probe, so the work doubled per level of nesting: `ir_v1::step_mono` (three levels) elaborated in 1,826 ms with the probe and 218 ms without it, `model::interpret_rr_opcode` 1,667 vs 637, `model::decode_rr_bytes` 532 vs 83; whole files at width one: ir_v1 4.45 s → 2.44 s, x86 model 11.5 → 9.2, function_ir 2.66 → 2.44, showcase 45.6 → 44.4, omega unchanged (no written motives). The nested re-probing is fixed: a probe clone sets `attempt.motive_redundancy_probe` and nested written motives are probed only by the real pass, once each (`step_mono` 1,826 → 1,197 ms; ir_v1 4.45 → 3.61 s; the nested warnings are still found, `warnings.rs`). What remains is the probe's own price — one extra elaboration plus one kernel check per written motive, paid in full when the motive is *not* redundant (none of ir_v1's are; the stdlib adopted its 58 omissions on 2026-08-22): `interpret_rr_opcode` is still 1,691 ms against 637, and ir_v1 1.2 s and the x86 model 1.7 s above their probe-free cost. The acceptance line "does not duplicate expensive kernel gates on declarations that cannot possibly qualify" has no cheap recognizer behind it today; whether this lint stays always-on or becomes a review-mode lint is the open question ([[lint-roadmap]]'s 2026-08-22 split of optional review advice from always-on warnings).
- 2026-09-17: 2026-09-17: review-mode. The lint's recognizer is a second elaboration plus a kernel check per written motive, paid in full on every motive a cleaned library retains, so it no longer runs in an ordinary check: `Elaborator::set_review_lints(true)` / `heather check --review` turns it on, and the warnings suite pins both the review-mode findings (single, nested) and the silence without it. Whole files at width one after this: ir_v1 4.45 s → 2.44 s, x86 model 11.5 → 9.4, function_ir 2.66 → 2.44. The user's verdict was that a lint whose recognizer is a re-elaboration is a review tool, with removal on the table if review mode goes unused; this issue stays open only for the inference-position candidates and the census rerun.
