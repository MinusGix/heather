---
title: Nat's arithmetic tail: min/max, the sub kit, and the order-interaction lemmas
status: open
labels: [stdlib,proofs,arithmetic]
created: 2026-08-17
updated: 2026-08-17
---

The half of [[nat-order-kit]]'s round that was deferred by charter rather than
by any obstacle, given an owner of its own so that the order issue can close.

`lib/std/nat.hthr` states the order in full and proves its kit. What it does
not have is the *arithmetic* that reads the order:

- **`min`/`max` at `Nat`** — plain structural recursions, no decider needed.
  (`std/algebra`'s `max_of` is a different thing: a `Cmp`-generic pick.)
- **The `sub` kit beyond `sub_zero`** — `add_sub_cancel`, `sub_add_cancel`
  under `n <= m`, `sub_self`, `sub_le`. `sub` and `sub_zero` are there;
  `le_add` already does the one `sub` fact the order needed and does it inline.
- **The order-interaction lemmas** — `add_le_mono`, `mul_le_mono`,
  `le_of_add_le_add_l`, and cancellation.

## Why it is separate rather than a line in the order issue

Two issues each named the other as the owner: [[std-api-waves]]'s wave-1 row
said the `sub` kit and `min`/`max` were deferred to [[nat-order-kit]], and
[[nat-order-kit]]'s "what is left" said wave 3 was the other half of the same
list. Circular ownership is how work becomes unfindable (README rule 1), and it
kept the order issue open long after its own scope had landed in full (rule 3).
This issue is the answer to "who owns it": here.

## What it assumes from elsewhere

- **[[nat-order-kit]]** owns the order. Assumed here: only that `Le`, `Lt` and
  their kit exist and are stated propositionally, which is what makes
  `sub_add_cancel` statable under a hypothesis `n <= m` at all.
- **[[std-api-waves]]** owns sequencing. Assumed here: nothing — this is a
  wave-3 item whenever wave 3 runs.

## Acceptance

The names above exist in `lib/std/nat.hthr` with proofs, and `min`/`max`
**reduce** at closed arguments (`max(2, 5)` is `refl`-provably `5`), which is
the property every recursion in that file is written to keep.
