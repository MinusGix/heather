---
title: Audit structural readers of lowered types against El-of-a-beta-redex
status: open
labels: [frontend,elaboration,robustness]
created: 2026-08-01
updated: 2026-08-01
---

From [[record-types-as-type-valued-functions]] (2026-08-01): the routing arm made the repro pass on first build, but the real consumer (RefinesOn in lib/ir_v1.hthr) then failed twice more in readers the issue never mentioned — `record_of` (resolve_dot's shape reader) and `unify_ty` (the congruence walk) both read a lowered type structurally and declined `El` of a **β-redex**, a shape no previous round could produce because a type had never before arrived through a `Val -> Type` function *value*. Both were repaired in that round (`record_of_at` with a one-step whnf fallback; `unify_ty` decoding its subject below the `El ?A` pattern rule — docs/record-type-values.md §4).

The lesson the round recorded: those two were found by a consumer, not an audit. This issue is the audit — a bounded sweep of the remaining structural readers of `Type` in crates/elab (the "readers" table in docs/types-as-expressions.md §4, now six entries and stated as an open list) against the β-redex-under-El shape, adding the decode fallback or a negative test to each. Small; the fix pattern is established twice over.
