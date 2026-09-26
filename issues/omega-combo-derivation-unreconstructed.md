---
title: omega finds a refutation through a Combo derivation it cannot reconstruct
status: open
labels: [omega,proofs]
created: 2026-09-26
updated: 2026-09-26
---

`omega` finds a refutation it then cannot certify:

```text
theorem combo(s, t, v: Nat, value: s = v, small: v < 1000, first: t = v + v,
    r0: s < nat::Nat::pow(2, 64), r1: t < nat::Nat::pow(2, 64)):
    2 * (t) + (0) < nat::Nat::pow(2, 64) + (0) { omega }
error: `omega` got stuck: Omega proof reconstruction does not yet support
derivation Combo { left: 3, left_scale: 1, right: 15, right_scale: 1 }
```

Without `value`/`r0` (the facts about the unrelated `s`) it checks. So the
search takes a route through the extra rows that the reconstructor doesn't
cover, even though a certifiable route exists.

Found 2026-09-26 through `bv_omega` ([[bv-omega-check-cost]]): a word a fact
in scope states (so a leaf) beside the range facts the tactic adds for every
leaf.

## Acceptance

- The repro checks.
- The reconstructor covers the `Combo` shape, or the search avoids emitting a
  derivation it cannot replay, with a control that such a derivation is still
  refused rather than trusted.
