---
title: omega ignores a fact whose type is a β-redex (an Exists's .proof)
status: open
labels: [omega,tactics]
area: tactics
created: 2026-10-29
updated: 2026-10-29
---

A fact whose type is a β-redex is listed among `omega`'s locals but not
reflected. The common case is the `.proof` of an `Exists`, typed
`(λ k => P(k))(e.witness)`. Probe on master 4f0ac27
([[proof-patterns-audit-2026-10]]):

```
theorem ex_proof(a: Nat, e: Exists<Nat>(λ k => a = k + 2)): 2 <= a { omega(e.proof) }
```

is refused. The report lists `__omega_fact_0: a = add(e.witness, 2)` (the
display contracts the redex, [[redex-spelled-as-contractum]]) but the atoms
are only `[a]`. The workaround recorded in memory (CutSat round, 2026-10-28)
is a typed `have` that restates the contractum.

## Wanted

Contract head β-redexes of a fact's type before reading it, the way the
unifier does since PR #62 (`spelling::beta_head`).

## Acceptance

- `ex_proof` closes with `omega(e.proof)` and with `e.proof` bound as an
  unannotated `let`, as probes in `lib/_tests/std/tactic/omega_tests.hthr`.
