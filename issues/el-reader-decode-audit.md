---
title: Audit structural readers of lowered types against El-of-a-beta-redex
status: closed
labels: [frontend,elaboration,robustness]
created: 2026-08-01
updated: 2026-08-01
---

From [[record-types-as-type-valued-functions]] (2026-08-01): the routing arm made the repro pass on first build, but the real consumer (RefinesOn in lib/certgen/ir_v1.hthr) then failed twice more in readers the issue never mentioned — `record_of` (resolve_dot's shape reader) and `unify_ty` (the congruence walk) both read a lowered type structurally and declined `El` of a **β-redex**, a shape no previous round could produce because a type had never before arrived through a `Val -> Type` function *value*. Both were repaired in that round (`record_of_at` with a one-step whnf fallback; `unify_ty` decoding its subject below the `El ?A` pattern rule — docs/record-type-values.md §4).

The lesson the round recorded: those two were found by a consumer, not an audit. This issue is the audit — a bounded sweep of the remaining structural readers of `Type` in crates/elab (the "readers" table in docs/types-as-expressions.md §4, now six entries and stated as an open list) against the β-redex-under-El shape, adding the decode fallback or a negative test to each. Small; the fix pattern is established twice over.

## Log

- 2026-08-01: Audit complete: full roster in docs/record-type-values.md §6; types-as-expressions §4 list is closed. Six readers repaired (record_of behind LetRecord, indexed_of x3 sites via step-and-retest indexed_of_at, vec lit/map/fold via decoded, wf_branch motive via one whnf in a rebuilt context, cong defensively), ~30 already-fine with stated reasons. No silent wrong results — all declines were loud. Key nuance recorded in §6.3: whnf is WRONG for Vec (reduces on length) and indexed families (reduce on index); the rule is structural first, then reduce as little as possible, retesting each step. Secondary finding: 4 of 6 were reachable via the delta spelling alone, latent since types-as-expressions. 16 tests (el_reader_audit.rs), full suite green, ir_v1 ~42s (no regression). Follow-up: [[goal-display-decodes]].
