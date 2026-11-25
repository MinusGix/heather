---
title: bv_omega and a window that fits: a word sum that may wrap, the spellings that are true, and the check that gives the proof
status: open
labels: [tactics,bitvec,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Met writing a push through the arena's `store` ([[arena-handles-push-and-new-vec]], log of 2026-11-25): a test in the code of the shape `base + len < 16` on words does not give `bv_omega` the fact the window's `fits` wants, `base.toNat() + len.toNat() <= 16`, so the proof had to come from the handle's invariant instead of from the test the code runs.

As stated the implication is false, and `bv_omega` is right to stop: a sum of words may wrap, and `(base + len).toNat() < 16` holds at `base = 2^64 - 1`, `len = 2`. So this is two questions, not one defect.

## Scope

- **Reproduce and classify.** The exact goal and hypotheses at the arena's push; which spellings of "the window fits" are true as natural-number facts (`len <= limit ∧ base <= limit - len`; a sum with a carry test; a sum of two words each known below `2^63`) and which of those `bv_omega` proves today. A table of probes in `lib/_tests`, each a theorem or a `¬` theorem.
- **Fix what is a gap.** Where a true spelling is refused, make `bv_omega` read it (the tactic takes a word apart through `add`, `sub`, `ofNat` and byte splits; `docs/proof-patterns.md` has what it cannot read yet), or record why not.
- **Say it when the model wraps.** Where `bv_omega` stops with a counter-model in which a word sum wrapped, the report should say that the sum may wrap and name a spelling that does not, since the reader's first guess is that the tactic is weak.
- **The check that gives the proof** (vision principle 13: a runtime check is a helper that discharges an obligation). A library function on words, compiled as a `runtime fn`, that tests whether `base` and `len` fit under a limit without wrapping and whose `True` answer yields the natural-number fact, found by a found proof (`:= bv_omega` or an evidence rule) under `if h: …`. The arena's push is the customer: its proof then comes from the test the code runs.

## Done when

The probe table is in the library, each true spelling is proved by `bv_omega` or has a recorded reason, a wrapping counter-model is reported as one, and a function of `Arena` that pushes after the fitting check compiles with its `store` proof found from that check.

## What it assumes from elsewhere

- **[[runtime-record-calls-erased]]** (closed) gives a record function calling `Arena::store` with a found proof.
- **[[bv-omega-word-arithmetic-modulo]]** owns masks and borrowing subtraction modulo a power of two; not this.
