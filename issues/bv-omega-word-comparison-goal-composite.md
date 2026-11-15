---
title: bv_omega does not take apart a composite word in a word-comparison goal
status: open
labels: [tactics]
area: tactics
created: 2026-11-15
updated: 2026-11-15
---

`theorem next_le(m, hi: u64, room: m < hi): m + 1 <= hi { bv_omega }` is
refused ("`omega` got stuck", `toNat(m + 1)` left an atom), while the same
claim over numbers, `(m + 1).toNat() <= hi.toNat()`, is proved. The two are
the same type (`BitVec::unsigned_le` is `a.toNat() <= b.toNat()`), so the
goal walk should read a word comparison as its `toNat` form and take its
operands apart, as it does for a comparison in scope.

The binary search example states its range lemmas over `toNat` for this
reason (`examples/binary-search/search.hthr`, `next_le`). In a large context
`bv_omega` also lost `j <= m` from `j < m + 1` and `m < hi`; a two-line lemma
with only those facts in scope (`le_of_lt_next`) proves it, which suggests the
walk's generalisation of a word restated by several facts is the cause.
