---
title: wlog through negation (signs) and at ordered carriers other than Nat and Int
status: closed
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

## Log

- 2026-11-09: Built on PR #503 (Minus: "implement that new issue").
  - `Rat::wlog_le`, `Dyadic::wlog_le`; `Int::wlog_nonneg`,
    `Rat::wlog_nonneg` and `by wlog_sign(x, neg, nn)`;
    `CReal::wlog_within(P, swap, e, he, near, m, n)` by `lt_cotrans` and
    `by wlog_within(m, n, e, he, swap, near)`.
  - Every form takes `over := [h…]`: hypotheses about the points reverted
    into the goal before the points are abstracted (Lean's
    `generalizing`, the `Revert` request, design §26), so the cases get them
    at their own points. Without it a split whose hypotheses mention the
    point could not use `wlog` at all.
  - Customer: `CReal::exp_rat_pos` (exp_law) is the nonnegative case plus a
    two-line reduction through `exp(a)·exp(-a) = 1`.
  - **Not rewritten, and why.** `Rat::err_in_nonpos` is about `x: K` in an
    ordered field reached through `map`, with the interval `[-M, c]` and the
    `Around` predicate: deriving it from `err_in_nonneg` needs negation
    carried through `map`, `Around` (no `around_neg` exists) and the bound's
    `|R - q|`, which is longer than the fifteen-line copy. `Format::nbr_at`
    and `rep_fit`/`rep_on_grid` (eft) have no second copy to remove: the
    negative arm *is* the transport (negate `x`, `s`, the grid facts and
    read `H_of_neg`), which a `wlog_sign` reduction would restate line for
    line.
  - **`PseudoOrder` sections:** a constructive pseudo-order has no
    totality, so there is no `wlog_le` to state; the tolerance form is the
    one that exists, and only `CReal` has it, as no section-generic client
    asked. `wlog` finds its lemma by the carrier's head name, so a section's
    carrier variable is not served; that waits for a client.
