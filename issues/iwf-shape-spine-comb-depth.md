---
title: Recursion over an m-member mutual group is still about m^1.6 after the signature is named and the sum balanced
status: open
labels: [elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-10-27
updated: 2026-10-27
---

Left by [[mutual-group-recursion-gate-cost]] once the signature was named
(`docs/iwf-named-signature-design.md` §4). Filed first as the comb: a
family's shape was a right-nested sum, so a structural recursion's step was
a case tree Θ(k) deep, its convoy motives named the label as an `inr` chain
that deep, and each arm evaluated the named index functions down the chain.
[[wide-inductive-balanced-sum]] (PR #214) balances every sum of eight or
more summands, mutual groups' member sums included, so that part is done.

What is left, measured on master with both (the `mutual_group` ring of
`crates/elab/benches/frontend/fixtures/intricate.rs` plus one `sizeᵢ` per
member and a `refl`; `heather check --timings`, release, width one, cloud
box, whole file):

| m | before both | named signature | both |
|---|---|---|---|
| 80 | — | ~1.6 s | 1.44 s (gate 0.93 s) |
| 160 | — | 6.1 s | 4.4 s (gate 3.2 s) |

About m^1.6 from 80 to 160 (queries ×3.1, kernel steps ×3.9).
`inductive/mutual-recursion` is 1.28 over 4..32, about 1.5 from 16 to 32.
Not attributed since the balancing: the step's arm count is Θ(m) and each
arm should now cost about log m, so a superlinear residue means something
per arm still grows with m.

Acceptance: an attribution (stack samples or counters at m = 80 and 160)
naming what still grows per arm, and either a fix that brings
`inductive/mutual-recursion` towards 1, or a recorded reason it cannot.
