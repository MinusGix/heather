---
title: Check the three hand-written branch binder-count tables against each other
status: open
labels: [kernel,code-health]
area: kernel
created: 2026-11-16
updated: 2026-11-16
---

How many universe, global and local binders each of the 65 code-recursor
branches sits under is written out by hand in three places:

1. `crates/kernel/src/subst.rs` `map_branches` (:1360), as `dep(u, g, l)` increments;
2. `crates/kernel/src/bounds.rs` `compute_*` (:466), whose `.under(k)` counts
   "must stay identical" to subst.rs's local column;
3. `crates/kernel/src/rec.rs` `branch_specs` (:621), the telescopes themselves.

The comments say they "must stay in sync", by review (`rec.rs:11`). What
checks them today: bounds.rs's skips are re-verified in debug builds by
running the real traversal, so a bounds drift fails the law suite, but only
on a skip it actually takes. Nothing compares `map_branches`' increments with
`branch_specs`' telescope sizes, apart from the identity-recursor typing test
exercising them end to end.

## Fix

- A unit test that builds `branch_specs` over a small Γ and asserts, branch
  by branch, that the telescope's (universe, global, local) counts equal the
  increment `map_branches` uses. This needs the increments as data, so lift
  them into one `const BRANCH_DEPTHS: [(u32, u32, u32); 65]` that
  `map_branches` reads.
- bounds.rs's local binder counts read the same table or the same traversal,
  as its global half already does ("no second binder table to drift").
  Then its "one drift hazard" paragraph goes.

Related: [[rec-ga-runtime-telescope-check-decision]] (runtime trust in the
tables; this is the build-time half). Found by [[kernel-comment-audit]].
