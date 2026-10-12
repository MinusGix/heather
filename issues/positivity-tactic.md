---
title: A positivity tactic over the evidence rules, handing linear leftovers to omega
status: closed
labels: [proofs,solver,arithmetic]
created: 2026-10-10
updated: 2026-10-11
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
- 2026-10-11: 2026-10-11: Landed as a tactic term (docs/positivity-evidence-design.md §10): infer's proposition search (locals, computation, evidence rules) with omega as the fallback only at subgoals the rules leave over, so `0 < a * b` from `2 <= a`, `5 <= b` is `Nat::mul_pos` with an omega proof per factor. Omega calls are bounded by a per-run stuck-goal memo; the cheap routes run no omega at all (tests count it). The parameter-default spelling `h: 0 < n := positivity` is [[named-arguments]]' parameter defaults, which owns it; nothing else is left here.
