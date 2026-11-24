---
title: omega knows nothing of Nat x % n and x / n at a divisor that is not a literal
status: open
labels: [proofs,omega,tactics]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

`omega` reads Nat `x % c` and `x / c` at a literal divisor `c` (a quotient
atom with its division facts, `omega_cert.rs`'s `NatMod`/`NatDiv` arms), but
at a divisor that is not a literal both are opaque atoms with no facts
(2026-11-24, probed):

```heather
theorem nat_mod_le(x, n: Nat): x % n <= x { omega }                 // stuck
theorem nat_mod_open(x, n: Nat, h: 0 < n): x % n < n { omega }      // stuck
theorem nat_div_open(x, n: Nat, h: 0 < n): x / n <= x { omega }     // stuck
```

`bv_omega` closed the same gap for words ([[bv-omega-word-remainder-quotient]])
by stating, beside each such atom, the laws as hypotheses written as source:
`r <= x`, and `d <= 0 ∨ r < d` / `d <= 0 ∨ q <= x`, disjunctions `omega`
splits only once refuting without splits has failed, so a goal that does
not need them pays nothing. The Nat laws exist (`DivMod::Spec` of
`n.divmod(d)`, `Nat::mod_lt`, `DivMod::rem_le`, `DivMod::quot_le`).

## What sharing would take

Not the same code: `bv_omega` writes `have`s before calling `omega`, while
`omega` reflects the context it is given. The cheap shape is the same idea
one level down: when reflection meets a non-literal `Nat::mod`/`Nat::div`
atom, the frontend wraps the goal in `have`s of those facts (one lemma call
each) and reflects again, as its splits re-enter it. Two things to decide:
whether the extra hypotheses widen every call's relevance layers (they
should join the layer of the atom that introduced them), and whether a
`d ≠ 0`/`0 < d` guard should instead select the plain fact over the
disjunction.
