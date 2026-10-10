---
title: A positivity tactic over the evidence rules, handing linear leftovers to omega
status: open
labels: [proofs,solver,arithmetic]
created: 2026-10-10
updated: 2026-10-10
---

A `positivity` tactic that proves `0 < e` by composing the evidence rules
from [[infer-proposition-evidence]] over `e`'s structure, including the
nonlinear cases omega cannot see (`0 < a * b`), and hands linear leftovers
to omega. Usable as a tactic term and as a parameter default
(`h: 0 < n := positivity`, which needs [[named-arguments]]' binder defaults).

`infer` stays the cheap, implicit route; this is the opt-in heavy one.

## Log

- 2026-10-10: Filed from [[positivity-evidence]] (Minus: "we'll probably want
  a specific positivity tactic eventually").
