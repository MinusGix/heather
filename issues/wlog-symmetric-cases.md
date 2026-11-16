---
title: Symmetric case splits proved once: wlog lemmas for order totality and sign
status: closed
labels: [stdlib,proofs,ergonomics,tactics]
area: mathematics
created: 2026-11-08
updated: 2026-11-09
---

A proof that splits on `m.le_total(n)` (or `le_dec`, `lt_total`, a sign
case) often proves the same thing twice with the roles swapped. Examples:

- `CReal::atanh_regular` (lib/std/analysis/real_log.hthr): the `Inl` and
  `Inr` arms are the same eleven lines with `m` and `n` exchanged.
- `Rat::err_in_nonneg` / `Rat::err_in_nonpos` (lib/std/num/float/float_real.hthr):
  two theorems, one per sign, whose bodies differ by which slope goes where.
- `Format::nbr_at` (lib/std/num/float/eft.hthr) and its kin, by the sign of
  `X` through negation.

There are about 245 order case splits (`le_total(`, `lt_total(`,
`le_dec(`, `lt_dec(`, `trichotomy(`) under lib/std/algebra, analysis and
num; not all are symmetric, but the symmetric ones double the proof and
the review.

## Direction

Library first; Heather's binders already express it:

```heather
theorem Nat::wlog_le(P: Nat → Nat → Type, sym: (a, b: Nat) → P(a, b) → P(b, a),
    le: (a, b: Nat) → a <= b → P(a, b), m, n: Nat): P(m, n)
```

and the same at `Int`, at any `PseudoOrder` through cotransitivity where the
constructive reading allows it (a `<=`-total carrier only: at `CReal` the
split is `le_or_lt` with a tolerance, so the lemma there takes the
tolerance), and a sign version through an involution
(`P(x) ↔ P(-x)` plus the nonnegative case). A `wlog` tactic that infers `P`
from the goal is the follow-up, by abstracting the two variables the way
the match-motive synthesis does; it is not needed to get the benefit.

## Acceptance

- `Nat::wlog_le` and `Int::wlog_le` in their type files, with
  `atanh_regular` rewritten as the customer (one arm plus the symmetry).
- `err_in_nonpos` derived from `err_in_nonneg` through negation, or a note
  in this issue saying why the slopes make that longer than the copy.

Related: docs/surveys/stdlib-math-awkwardness-survey.md §9.

## Log

- 2026-11-09: Done as the tactic directly (Minus: "we can just add wlog").
  `Nat::wlog_le` and `Int::wlog_le` in their type files; `by wlog(m, n,
  swap, le)` (lib/std/tactic/wlog.hthr) abstracts `m` and `n` out of the
  goal into `P` and applies the carrier's `T::wlog_le`, with the two cases
  written as unannotated `λ`s checked where the lemma puts them. Host side
  (docs/metaprogramming/host-elaboration-interface-design.md §26): an `Abstract` request,
  and quoted arguments held as surface syntax when they infer no type.
  `CReal::atanh_regular` is the customer: one arm plus a five-line swap.
  Probes in lib/_tests/std/tactic/wlog_tests.hthr. The sign version
  through negation (`err_in_nonpos` from `err_in_nonneg`, `Format::nbr_at`)
  and the `PseudoOrder`/`CReal` versions are [[wlog-sign-and-ordered-carriers]].
