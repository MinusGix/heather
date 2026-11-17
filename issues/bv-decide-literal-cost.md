---
title: bv_decide: cheaper hinted literals in the LRAT checker
status: open
labels: [bitvec,solver,tactics,perf]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

Each hinted literal costs a few hundred kernel steps: a lookup of its variable in the assignment trie, a lookup of the hinted clause by id in the formula trie, and an assignment rebuilt per unit (`lib/std/tactic/lrat.hthr`, `rup`, `hinted`). Every claim pays it.

Ideas: check a chunk against one assignment every step extends rather than building it from `MEmpty` per step; number variables and clause ids so what is used together sits close (shorter trie paths); measure which of the two lookups dominates first. Measured and rejected: a big `Nat` bitmask as the assignment (division by large powers of two is slow in the kernel; a fast bit test would be a kernel acceleration question, [[kernel-acceleration-policy]]).

Parent: [[lrat-certified-bitvector-decision]].
