---
title: omega splits a conjunction fact one level only
status: closed
labels: [omega,tactics]
area: tactics
created: 2026-10-29
updated: 2026-10-29
---

`omega` splits a conjunction fact one level only. Probe on master 4f0ac27
([[proof-patterns-audit-2026-10]]):

```
theorem conj2(a, b, c: Nat, h: a < b ∧ (b < c ∧ c < 5)): a < 5 { omega }
```

is refused: the model is `[a = 5, b = 6]` with `c` never read, so the inner
`And` is skipped. The workaround recorded in memory since 2026-10-21 (float
rounding round) is to bind `.left`/`.right` as lets by hand.

## Acceptance

- `conj2` closes, and so do a right-nested and a left-nested three-way
  conjunction in a fact, as probes in `lib/_tests/std/tactic/omega_tests.hthr`.
- The certificate cites the projections it used (`h.right.left`), so an
  unused conjunct costs nothing in the kernel.

## Resolution (2026-10-29)

`local_facts` (`crates/elab/src/omega_cert.rs`) lists a conjunction fact as
its conjuncts at every depth, each named by its projection path and typed by
`project_field`; the certificate cites `h.right.left` only where it uses it.
A disjunction under a conjunction is split like a top-level one. Design:
`docs/omega-measure-reduction-design.md` §13. Probes and a control:
`conj_*` in `lib/_tests/std/tactic/omega_tests.hthr`.
