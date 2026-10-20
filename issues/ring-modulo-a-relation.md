---
title: Normalize ring identities modulo a relation
status: open
labels: [proofs,solver,algebra,setoids]
area: tactics
created: 2026-10-20
updated: 2026-10-20
---

`ring` normalizes at `Int` and `Nat` and proves `Rat` laws only through
cross-multiplication, because its normalizer and soundness proof
(`lib/std/ring.hthr`) are stated over `Int` with `=`. A goal
`x * (y + z) ≈ x * y + x * z` at `Rat` is proved today by unfolding `≈` to an
`Int` equation and asking `ring` there, with the denominators handed in as
facts.

`CommRing<A>(≈, +, *)` (lib/std/semiring.hthr) is now the interface that
normalization wants: restate `RingExpr::eval`, `RingPoly::eval` and the
soundness lemmas over a commutative ring modulo its relation, so a
certificate reads `≈` at `Rat` (and at `CReal`, once it is a ring) without
crossing to `Int`. The coefficient embedding (`Int → A`) is the one new piece
the interface does not carry; it belongs to the carrier, as `of_nat` does in
`OrderedField`.

## Acceptance

- `ring` proves a `≈` goal at `Rat` directly, and the `Int`/`Nat` paths keep
  their certificates' shape (or the cost change is measured with
  `scripts/perf ab`).
- The soundness proof uses only the `CommRing` layers, `Respects2` through
  `rel_cong`, and the embedding's laws.

## What it assumes from elsewhere

- **[[semiring-ring-structure-api]]** owns the layers. Assumed here: only that
  `CommRing(≈, +, *)` gives a commutative ring modulo `≈`.
- **[[ring-certificate-kernel-cost]]** owns the certificates' cost.
