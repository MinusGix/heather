---
title: Implement weak-head reduction to WHNF/neutral (ch. 06)
status: open
labels: [kernel, delam]
blocked-by: [kernel-substitutions]
created: 2026-07-22
updated: 2026-07-22
---

Untyped single-step reduction `⇝` and its closure to weak head normal
form, per ch. 06:

- WHNF/neutral classification for types and terms (the `W/V/w/ν` grammars).
- Type reduction: only the `El` decode rules (`El 0 Nat ⇝ Nat`, etc.) plus
  congruence into the encoding.
- Term reduction: β for elimNat, app, `$`, ctx-app, ty-app, both letboxes,
  and the 13 recursor cases (each instantiates the branch telescope —
  depends squarely on substitutions being right).
- Congruence rules at head positions only; for `ElimCodeTm`, the paper
  fixes type-then-term reduction order — keep that choice.
- Blocking: recursors are neutral on neutral scrutinees AND on
  `box (U^δ)` / `box (u^δ)`.

Determinacy is a good cheap test: reduce with a fuel bound and check the
WHNF is stable; golden tests for each β-rule shape.

## Log

- 2026-07-22: Ready to start: substitutions landed (d4a81e2). Implementation pointers: beta for app/elimN via LocalSubst::id(ctx).extended(arg); letbox beta via GlobalSubst::single; recursor branch beta needs multi-entry GlobalSubst matching the branch telescopes (entries outermost-first, see Branches docs in term.rs) plus universe subst for the branch's level vars. Blocking behavior: recursors stuck on neutral scrutinees AND box(U^delta)/box(u^delta). Run tests only via scripts/test.
