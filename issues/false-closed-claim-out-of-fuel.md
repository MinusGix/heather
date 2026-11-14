---
title: A false closed claim is refused OutOfFuel, not as a mismatch
status: open
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
