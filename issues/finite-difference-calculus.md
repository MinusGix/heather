---
title: Difference calculus: telescoping, summation by parts, binomial theorem
status: closed
labels: [stdlib,mathematics,analysis]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-11-01
---

Layer A′ of `docs/library/analysis-foundations-design.md` (§4): the exact discrete
calculus, at a commutative ring and without division.

Scope:

- `Δf(k) = f(k+1) - f(k)`; telescoping `∑_{k<n} Δf ≈ f(n) - f(0)` and its
  order form (`Δf <= g` gives `f(n) - f(0) <= ∑ g`);
- summation by parts;
- falling factorials and `Δ x^{\underline m} = m · x^{\underline{m-1}}`, with
  the power-sum closed form multiplied out;
- the geometric sum `(1 - r) · ∑_{k<n} r^k ≈ 1 - r^n`;
- binomial coefficients, the binomial theorem at a commutative semiring
  (through `of_nat`), Vandermonde;
- Newton's forward-difference formula, the discrete Taylor theorem.

Acceptance: `Series::decay` (or its core) is restated as an instance of the
geometric lemma; the binomial theorem is proved generically and probed at
`Nat`, `Int`, `Rat`.

## What it assumes from elsewhere
- **[[finite-sums-and-products]]** owns the range sum and its reindexing lemmas.

## Log

- 2026-11-01: Landed as `lib/std/algebra/difference.hthr` (probes `lib/_tests/std/algebra/difference_tests.hthr`). `GroupRel::delta`/`delta_pow` at an abelian group; `GroupRel::telescope` and its order form `LocatedAddGroup::telescope_le`; `Nat::choose` (in `nat.hthr`, Pascal's rule by computation) with `Semiring::of_nat` as the cast; one lemma carries Pascal's rule through a sum (`Semiring::pascal_range`, square case `pascal_step`) and the binomial theorem (`CommSemiring::binomial`), Newton's formula (`CommRing::newton`) and Hurwitz's Leibniz rule are each that lemma and an induction; `CommRing::sum_by_parts`, `CommRing::geometric`, falling factorials (`Ring::falling`, `Ring::delta_falling`, `Ring::falling_sum`) with `CommRing::sum_id` and `CommRing::sum_squares` multiplied out; `Nat::vandermonde`. Acceptance: the binomial theorem is generic and probed at `Nat`, `Int`, `Rat` (and at `Hurwitz<Rat>`); `Series::decay` is now an instance of the geometric bound `OrderedField::geometric_le` at ratio one half (`Series::err_half`, `Rat::half_pow`). Two `ring` readings were needed: a range sum at a class carrier's own `+`/`*` (crates/elab/src/ring.rs `range_step`), and `Ring::nat_cast<K>(numeral)` as a constant. Not done: power sums through Stirling numbers in general (the first two are closed forms).
- 2026-11-01: Filed [[rel-sym-swapped-blames-dictionary]]: a swapped `rel_sym` under a `∏` at an ordered field is reported as a dictionary mismatch at the statement.
