---
title: Finite sums and products over a commutative monoid modulo ≈
status: closed
labels: [stdlib,mathematics,analysis]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

Layer A of `docs/analysis-foundations-design.md` (§4): finite sums and
products as folds over a commutative monoid modulo its relation, with one
theorem serving `∑` and `∏` through the semiring layers' `multiplicative` tag.

Scope:

- the range sum `MonoidRel::range(op, n, f)` by recursion on `n` (the shape
  `Series::sum` already has), and sums over `Fin(n)`, lists, rectangles,
  triangles and antidiagonals defined through it;
- laws modulo `≈`: congruence, split/shift, empty and singleton, reverse,
  permutation invariance (commutative), rectangle Fubini and the
  triangle-to-antidiagonal exchange, distributivity at a semiring;
- order laws at `OrderedAddGroup`: monotone, nonnegative, `|∑ f| <= ∑ |f|`;
- a carrier-level spelling (`Rat::sum(n, f)` or similar) until the binder
  production exists; probes in `lib/_tests` at `Nat`, `Rat` and an open carrier.

Acceptance: `Series::sum` is shown to be the range sum (a theorem, no
rewrite of series.hthr required), and the exchange lemma proves one
Cauchy-product coefficient identity at `Rat`.

## What it assumes from elsewhere
- **[[big-operator-semantics]]** owns the semantic comparison; assumed here
  only its finite route (generic folds), which the design note recommends.
- **[[notation-extensibility]]** owns the `∑ k < n, e` production; nothing here waits for it.
- **[[finite-set-enumeration-and-folds]]** owns folds over finite sets; assumed
  here only that an enumeration is a list.

## Log

- 2026-10-27: LANDED: `lib/std/algebra/big_operator.hthr`. `MonoidRel::range(op, n, f)`
  by recursion on `n`, built at the end; lists through `List::range(n)`
  (`range_fold`), the antidiagonal `MonoidRel::antidiag(op, n, f)`, rectangles
  and triangles as ranges of ranges. Laws, each one theorem for `∑` and `∏`
  (products through a semiring's `multiplicative` tag): `range_cong` (termwise
  below the bound), `range_eq`, `range_unit`, `range_one`, `range_add`
  (split/shift), `range_succ_l`, `range_single` (one non-unit term); with
  commutativity `range_op`, `range_swap` (Fubini), `range_perm` (a bijection
  below `n` given with its inverse, proved by spreading each term over a row
  with the Kronecker delta `MonoidRel::at`, summing the square the other way,
  and reading one term per column, so no index surgery), `range_reverse` (an
  instance of `range_perm`), `range_antidiag` (triangle to antidiagonals); at a
  semiring `mul_range_l`, `range_mul_r`, `range_mul_range`, `range_cauchy`; at
  `LocatedAddGroup` `range_le`, `range_nonneg`, `range_abs_le`. The order laws
  sit at `LocatedAddGroup`, not `OrderedAddGroup` as scoped: adding two `≤`s
  needs cotransitivity (`LocatedAddGroup::add_le_mono`).

  Carrier spellings `Nat::sum`/`prod`, `Int::sum`/`prod` (big_operator, beside
  the instances in semiring), `Rat::sum`/`prod` with `Rat::sum_abs_le`
  (`|∑ f| <= ∑ |f|`), `CReal::sum`/`prod`. They are needed, not only
  convenient: a bare `MonoidRel::range(+, n, f)` at a concrete carrier is
  refused on the left of `≈`, `=` or `+` (the operator's carrier is resolved
  before the call's `A` is known), so the `∑` production must elaborate its
  body first (logged on [[notation-extensibility]]). Acceptance:
  `Series::sum_is_range` (`s.sum(k) = Rat::sum(k, …)`, an equation, series.hthr
  untouched otherwise), and `lib/_tests/std/algebra/big_operator_tests.hthr`
  proves the Cauchy-product coefficient identity at `Rat` at open sequences
  and evaluates it at `a = b = (1, 2, 3)` (coefficients 1, 4, 10; both sides
  15), with probes at `Nat`, `Int`, `CReal`, an open commutative monoid and
  an open semiring. No `Fin` type exists; the `k < n` hypotheses are its role.
  Side additions: `or_pick_dec_not` (logic), `Nat::sub_succ_lt` and
  `Nat::sub_succ_sub_succ` (nat), `List::range`/`len_range` (list).


- 2026-10-27: The `∑`/`∏` binder landed on top of this (logged on
  [[notation-extensibility]]): `∑ k < n, e` is `MonoidRel::range(+, n, λ (k:
  Nat) => e)`, and the carrier comes from the body. The per-carrier spellings
  (`Nat/Int/Rat/CReal::sum`/`prod`) are gone; the library's statements, the
  probes and `Series::sum_is_range` (`s.sum(k) = ∑ i < k, s.term(i)`) are
  written in the notation. `Rat::sum_abs_le` stays, as
  `(∑ k < n, f(k)).abs() <= ∑ k < n, f(k).abs()`.
- 2026-10-27: Nested calls under `∑` no longer need annotated λ binders:
  `MonoidRel::antidiag(+, n, λ i k => …)` infers `i`, `k` from `f`'s domain
  (docs/unifier-completeness-design.md, amendment 2026-10-27); the
  big_operator probes are written unannotated.
