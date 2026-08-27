---
title: Avoid exposing structural twice as bitvector proof control
status: open
labels: [stdlib,proofs,arithmetic,bitvec]
created: 2026-08-26
updated: 2026-08-26
---

Follow-up to [[bitvec-executable-carry-correspondence]]. The bitvector
implementation deliberately uses `nat::twice` as a cheap executable one-bit
shift, avoiding open unary multiplication and large closed numeral reduction.
Its correspondence proof currently leaks that representation choice into
proof control through `TwiceLeTwice`/`TwiceLeOdd` and the dedicated twice order
lemmas. Prefer a future proof interface where ordinary linear arithmetic or a
representation lemma bridges the executable recurrence without tactics or
callers recognizing `twice` specially. This does not require changing
`BitVec.toNat`'s executable normal form now; it records that structural twice
should not become a privileged Omega frontend construct merely because the
current carry proof exposes it.
