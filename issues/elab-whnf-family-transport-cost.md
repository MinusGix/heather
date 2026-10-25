---
title: Elaborator whnf through a W-form family's stored-children transport is slow
status: open
labels: [elaboration,performance,indexed-families]
area: language
milestone: [math-metatheory]
created: 2026-10-25
updated: 2026-10-25
---

On the `IWf`-on-`W` route (`docs/iwf-infinitary-design.md`), a constructor
with two or more recursive fields stores its children's trees `k̄` and an
equation `Id(ρ(k̄); f)`. A `match` arm on it transports along that equation
(§7, `J₂`), and along the index equation (`J₁`). On a literal constructor
both proofs are `refl` and the `J`s compute.

`SemanticOracle::whnf_term` reaches the head of such a reduct quickly with
the value probe. When the head is a constructor, it then respells the
reduct with the substitution reducer (`reduce::whnf_term_delta`) at full
fuel, copying the transports' annotation-heavy terms at each step. This is
the residual [[elab-whnf-copies-straight-continuations]] names for types,
here for terms.

Measured once, as a shape: a plain `cong` in the `k̄` arm of
`cp_size`-style induction (`sz(n, cp(n, t)) = sz(n, t)`,
`crates/elab/tests/iwf_no_confusion.rs`) spends nearly all its time in the
two whnfs of `cong`'s second attempt, enough to dominate the test binary.
The same arm with the endpoints stated (`succ_eq(…, cs(m, l))`) needs no
whnf of the goal. One-child arms are cheaper by more than an order of
magnitude but are still dominated by the same whnf.

Options:

1. Respell from the value graph rather than re-reducing by substitution
   (the general fix both issues point at).
2. Make the transports cheaper to reduce: `J₂` generalizes `CH(g)` and the
   ih along `Id(ρ(k̄); f)`, so its motive is large. An encoding whose arm
   reads the children from `k̄` directly would shrink what is copied.

## Log

- 2026-10-25: Filed from the inversion round
  ([[cong-inference-through-iwf-w-children]]).
