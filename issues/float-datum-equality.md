---
title: Settle the float library's two equalities (IEEE vs datum)
status: open
labels: [mathematics,floating-point,design]
area: mathematics
milestone: [math-float]
created: 2026-11-26
updated: 2026-11-26
---

The float library has two equalities of `Float(F)`: `Float::Same`
(`round.hthr`; IEEE comparison, so NaN is unequal to itself, used by the
rounding uniqueness theorems) and `Float::SameDatum` (`p3109_codes.hthr`;
identity of data: same value, same infinity, or both NaN, used by the code
bijection). Both are right for their uses, but nothing says which a theorem
means, and the names do not say it either.

Decide the convention: likely `SameDatum` as the default for round trips and
specifications, `Same` renamed to say it is IEEE equality, and each stated
as an `Equivalence` (or, for IEEE's, a partial one), with the lemma that they
agree off NaN. Update docs/library/floating-point-design.md §4.
