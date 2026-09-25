---
title: Crossing certificates: each link costs more than the one below, quadratic in chain depth
status: open
labels: [x86,certificates,performance]
created: 2026-09-25
updated: 2026-09-25
---

In a crossing certificate (design `docs/native-first-program-design.md`
§10.1), each link of a composed helper chain costs about 40K kernel steps more
than the link below it. The continuation's instantiation walks the chain once,
so a chain of depth `d` costs quadratically in `d`. It is 432K steps at the
root of the 16-link decimal formatter, within fuel. If the growth stays quadratic, it reaches the
per-declaration fuel (2^20 steps) at around depth 24. Larger programs compose deeper than 16.

Owned here because it was the round's residue and had no owner
(`issues/README.md` rule 3).

## Questions

- Which term does the instantiation walk? Probably `{n}_carry(values, s)`
  instantiated at a valuation that is itself built from the prefix's
  valuation, so each level re-spells the chain below. `--only` on one link at
  growing depth plus a `Conv::tm` trace will name it.
- Can the generator name the instantiated valuation once per level, as it
  names crossings, so each level mentions its parent by name?

## Acceptance

- Link cost is flat in depth on the `place` chain (a table of per-link steps
  at depths 4, 8, 16, 32), with counts pinned in a test.

## What it assumes from elsewhere

- **[[valuation-lookup-case-step-cost]]** owns the other residue from the same
  round, the per-lookup cost.
