---
title: Implement weak-head reduction to WHNF/neutral (ch. 06)
status: closed
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
- 2026-07-22: Implemented in crates/kernel/src/reduce.rs: step_type/step_term (El decode, 8 core beta, all 13 recursor branch betas, congruences with the paper's type-then-term order for ElimCodeTm), fuel-bounded whnf_type/whnf_term, and W/V/w/nu classification predicates. Added instantiation-form universe substitution (Level::inst_at + Term/Type::inst_univ) since apply_univ is total but ULam/branch beta must renumber ambient level vars. Note one deliberate divergence: is_neutral_term requires ElimCodeTm's type annotation to be WHNF (the paper's nu-grammar leaves T unconstrained, but its own congruence order still reduces such terms, and neutrals must not step). tm_lam beta reads the return type off the WHNF Pi annotation. Tests: golden per beta-rule probing each branch telescope, blocking/ordering tests, and generator properties (normal forms don't step; reducts stay well-scoped under id-substitution); generators moved to tests/common/mod.rs for reuse.
