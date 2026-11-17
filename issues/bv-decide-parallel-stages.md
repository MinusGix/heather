---
title: bv_decide: check a refutation's stages on every kernel worker
status: open
labels: [bitvec,solver,tactics,perf,kernel]
area: tactics
created: 2026-11-17
updated: 2026-11-17
---

A refutation is one term, so one kernel worker checks it: 64-bit `x + y = y + x` is about 22 s on one core while the other seven idle. Two routes, each general:

- a tactic hands back auxiliary declarations (its stages as stage theorems), which the gate already checks in parallel;
- the gate checks the independent `refl` obligations of one term in parallel.

Either should cut wall time several-fold. The first is a host change; the second a kernel gate change. Parent: [[lrat-certified-bitvector-decision]].
