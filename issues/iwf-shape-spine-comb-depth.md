---
title: An IWf step's case tree is a comb over the shape spine, so a k-constructor family's recursion costs about k^1.8
status: open
labels: [elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-10-27
updated: 2026-10-27
---

Left by [[mutual-group-recursion-gate-cost]] once the signature was named
(`docs/iwf-named-signature-design.md` §4). A family's shape is a right-nested
sum, one summand per constructor, so the step of a structural recursion is a
case tree of depth Θ(k): each level's convoy motive names the label as a
chain of `inr`s as deep as the level, and each arm's conversion evaluates the
named index functions at its label down the same chain. An m-member ring
(two constructors each) is about m^1.8 from 24 to 160 members, with
`f#rec`'s per-level motive checks and the arms dominating; a single wide
inductive's `match` has the same comb (`inductive/isa-opcode-match`, ~1.3).

A balanced spine (a sum tree of depth log k) would make the label chains and
the tree's depth logarithmic. It is the constructor encoding of every
inductive, so it touches lowering, constructor values, `match`, inversion,
readback and export alike; nobody needs it yet beyond the bench.

Acceptance: a decision first (balanced spine, or a different step shape such
as a direct `k`-way case on a label code), recorded in a design note, before
any implementation.
