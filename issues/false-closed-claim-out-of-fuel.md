---
title: A false closed claim is refused OutOfFuel, not as a mismatch
status: closed
labels: [kernel,diagnostics]
area: language
created: 2026-11-14
updated: 2026-11-14
---

Split from [[surface-gaps-from-sha256-proof]] item 7. A false closed claim,
`digest(abc) = digest(abd)`, spends the conversion's whole step budget and
is refused `OutOfFuel`. A mismatch would be the honest answer.

**Why it is open:** a true claim `digest(abc) = digest(abc)` is decided at
once, because both sides are the same term. A false one is not: the two
sides are calls of one function on different arguments, which may still be
equal, so the only sound answer comes from evaluating both to normal forms
and comparing them. That evaluation (about a million steps) is larger than
the per-conversion budget, so the conversion gives up before it can see the
difference. To answer with a mismatch, the evaluation of closed terms would
need a budget of its own, or a faster route (native word runs already cost
one unit each), and then the kernel would need to report that two rigid
values differ. That is a kernel change.

**What is done:** the refusal now sits at the claim and names the part that
differs (`MismatchNotes::fuel_note`, "which differs at `99` against
`100`"), checked by `abd_claimed` in
`lib/_tests/native/crypto/sha256_stream_agreement_tests.hthr`.

## Resolution (2026-11-14)

Not a kernel change after all: the verdict stays the gate's, and only what
the refusal says is in question. A declaration refused `OutOfFuel` is now
checked once more at eight times the budget (`Refusals::kernel_refusal`,
`REFUSAL_FUEL_FACTOR`), on the refusal path only, and the refusal says what
that found:

- refused there as a mismatch: "with 8 times the budget the kernel computes
  both sides and finds them different: the claim is false" (`abd_claimed`
  in `lib/_tests/native/crypto/sha256_stream_agreement_tests.hthr`);
- accepted there: "the proof is right, but checks only with up to 8 times
  the budget: split the computation into stage theorems"
  (`sha256_abc_twice_at_once` in `lib/_tests/std/crypto/sha2_tests.hthr`);
- out of fuel again: the refusal is as before.

Measured: one SHA-256 digest of "abc" by `refl` costs 916,295 steps, just
under the budget, and the false claim `digest(abc) = digest(abd)` is decided
not convertible at 3,635,884: about four digests where computing both sides
is two. The conversion re-evaluates on the way (the δ-lazy same-head
attempt comparing spines that differ deep inside, unfolded one layer at a
time). Evaluating both closed sides to values first and comparing them
would halve it; that is a kernel question, not filed until a proof needs it.
