---
title: wlog through negation (signs) and at ordered carriers other than Nat and Int
status: open
labels: [stdlib,proofs,ergonomics,tactics]
area: mathematics
created: 2026-11-09
updated: 2026-11-09
---

[[wlog-symmetric-cases]] added `by wlog(m, n, swap, le)` over a carrier's
`T::wlog_le` (`Nat`, `Int`). Two shapes from that issue are still proved
twice:

- **Sign symmetry through an involution.** `Rat::err_in_nonpos` repeats
  `Rat::err_in_nonneg` (lib/std/num/float/float_real.hthr) with the slopes
  swapped, and `Format::nbr_at` (lib/std/num/float/eft.hthr) and its kin
  split on the sign of `X`. The lemma is `P(x) → P(-x)` plus the
  nonnegative case; the tactic is the same `Abstract` over one point. Check
  first whether rewriting `err_in_nonpos` through negation is shorter than
  the copy (the slopes trade places, so the reduction must move them); if
  not, note why here and close.
- **Other ordered carriers.** `Rat` has a decidable total order, so a
  `Rat::wlog_le` is the same three lines. At `CReal` the split is
  `le_or_lt` with a tolerance, so its lemma takes the tolerance; at a
  `PseudoOrder` section the lemma goes through cotransitivity. `wlog` finds
  `T::wlog_le` by the carrier's head name, so a section's carrier variable
  needs another lookup (the class's lemma).

Only the order case and the two integer carriers exist today.
