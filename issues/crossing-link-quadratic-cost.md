---
title: Crossing certificates: each link costs more than the one below, quadratic in chain depth
status: closed
labels: [x86,certificates,performance]
created: 2026-09-25
updated: 2026-09-25
---

In a crossing certificate (design `docs/archive/native-first-program-design.md`
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

## Log

- 2026-09-25: The premise does not reproduce on the current tree. The valuation `Nat::leb` tree ([[valuation-lookup-case-step-cost]], f86941e5) landed after this issue's measurement (435ab708). Port ids grow with depth, so a lookup that peeled the id grew too, which is the likely cause. The old binary was not re-measured. `place` chains certified by `compile-x86` (probes/link, width one) now cost the same at every level at depths 4, 8, 16 and 32: `_link_at` 3,400 steps, `_carry_at` 1,142, `_link` 82. `_correct` is 11–16K and drifts by about 120–240 steps a level, which is linear and small. Depth 32 certifies, past the predicted wall at 24.

  The real residue was a single link. In `decimal_line::line_word`, the crossing at `raise(n)` was one `refl` of 545,162 steps, half the fuel. Nested helpers (`raise` → `times256` → `double`) share their result port, and the reflector kept only the innermost body per port, so the `raise` crossing found no meaning over its child and fell back to unfolding all 40 doublings. Now every layer's body is kept (`function_ir_cert::SourceBodies`), and the crossing picks the one that reads its child. That link costs 97 steps plus a 23,275-step `_link_at`, the same as its `times256` siblings. The `line_word` certificate module went from 21.44M to 20.94M steps. `crates/elab/tests/crossing_link_cost.rs` pins both: link costs are identical across depths 3 and 8, and a nested helper's link stays below its `_link_at`s. Without the fix it fails, with `oct`'s link at 15,606 steps.
