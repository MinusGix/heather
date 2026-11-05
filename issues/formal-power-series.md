---
title: "Hurwitz series and jets: calculus in coinductive form"
status: open
labels: [stdlib,mathematics,analysis]
area: mathematics
milestone: [math-reals,ml-layers]
created: 2026-10-27
updated: 2026-11-01
---

Layer B of `docs/analysis-foundations-design.md` (§5), with the
representation decided in §3.4. A series is its coefficient function in the
Hurwitz convention (`coeff(n)` stands for the `n`-th derivative at the
point, with no factorial), the derivative is the shift, and bisimulation is
the proof principle. Everything computes at `Int` and at `Rat`.

Scope:

- `Hurwitz<A> { coeff: Nat → A }` over a commutative ring, with
  coefficientwise `≈`, pointwise `+`, and the product as binomial
  convolution over a named `antidiag(n)` (the transseries hook, §11);
  a `CommRingOfInt` instance so `ring` works on series;
- `Hurwitz::coind`: equal heads and bisimilar derivatives give `≈`, proved
  by induction on the index; the Leibniz rule for the shift;
- definitions by ODE as course-of-values recursion: `exp`, `sin`, `cos`
  over `ℤ`, with `s² + c² ≈ 1` and the `exp` addition law (one-variable
  form `exp(a·t)·exp(b·t) ≈ exp((a+b)·t)`) by coinduction;
- polynomials (degree bound as data) and `Jet(A, N)`, with truncation a
  ring homomorphism; composition when `coeff(0) ≈ 0`;
- Newton lifting for inverses (unit constant term) and simple roots;
- the bridge to ordinary power series over a ℚ-algebra (`a_n / n!`);
- dual numbers: evaluating a polynomial at `x + ε` gives `(f(x), f'(x))`,
  the forward-mode AD theorem `ml-layers` wants.

Codata is not the representation in this round: the Leibniz product is
corecursion up to `+`, which Heather's guard refused when this was filed.
Since 2026-11-02 it is accepted for a monomorphic series type
(`docs/codata-elaborator-design.md` §5.5, the Hurwitz product up to stream
addition, observations by `refl`); a series generic over a ring needs a
polymorphic friend with the ring's class binder
([[codata-up-to-friends-round-2]]).

## What it assumes from elsewhere
- **[[finite-sums-and-products]]** and **[[finite-difference-calculus]]**:
  the exchange lemmas and the binomial coefficients with Pascal's rule.
- **[[ring-modulo-a-relation]]**: `ring` at a carrier's `≈`.

## Log

- 2026-11-01: First round, `lib/std/algebra/hurwitz.hthr` (probes `lib/_tests/std/algebra/hurwitz_tests.hthr`). Done: `Hurwitz<A> { coeff }` at a commutative ring with coefficientwise `Hurwitz::Same`; `add`/`neg`/`scale`/`constant`; the shift `d` and `cons` with the two FTC laws by definition; the product as binomial convolution over `MonoidRel::antidiag`; the Leibniz rule (`Hurwitz::leibniz`, Pascal summed); bisimulation `Hurwitz::coind` (a relation closed under `d` that relates heads relates only equal series, by induction on the index), `Hurwitz::ext`, `constant_of_d`, `linear_unique` (`F' = c·F` has one solution per head). Every ring law of the product is coinductive: head by `ring`, derivative through Leibniz and the law one index down over all series at once (`mul_comm_at`, `mul_assoc_at`, `one_mul_at`), so no multinomial identity is needed. `instance CommRing` and `CommRingOfInt` at `Hurwitz<A>` (integers through `constant`), with `≈`/`+`/`*` designations, so generic theorems apply to series (`CommSemiring::binomial` at `Hurwitz<Rat>`), series nest (`Hurwitz<Hurwitz<Rat>>` resolves), and `ring` works on series (needed `ring` to read a carrier whose designated operations take section parameters, crates/elab/src/ring.rs `Op::GlobalAfter`). `exp(a·t)` with `exp_add` by `linear_unique` (read at one coefficient it is the binomial theorem, probed as such); `sin`/`cos` by a pair recursion with `sin² + cos² ≈ 1` over any commutative ring; jets as `Hurwitz::SameUpTo(N, …)`, respected by `+` and `*` (truncation is a ring morphism onto the quotient), and the dual-number product `Hurwitz::mul_first`. Everything computes at `Int` by `refl`.

  Still open in this issue: polynomials with a degree bound as data; composition when `coeff(0) ≈ 0`; Newton lifting for simple roots of a polynomial (the inverse case is done, below); the bridge to ordinary power series over a ℚ-algebra; the forward-mode AD theorem for polynomial programs (evaluation at `x + ε` gives `(f(x), f'(x))`, beyond the product rule `mul_first`); jets as finite vectors to compute with, and the refl-cost comparison the slice asks about.

  Newton lifting for inverses also landed in this round: `Hurwitz::Vanishes(m, e)` (order at least `m`), `Hurwitz::mul_vanishes` (orders add under `*`), the step `Hurwitz::newton_inv` with `1 - f·g' ≈ (1 - f·g)²` by `ring` at `Hurwitz<A>` (`Hurwitz::newton_inv_error`), and `Hurwitz::newton_inv_lifts`: from an inverse of the head, `k` steps invert `f` to order `2^k`. Probed at `Int` on `exp(t)`, where three steps agree with `exp(-t)` below order 8 and one step is visibly short.
- 2026-11-05: gardener: cites a file it shares with [[kernel-coinductive-types]] (`docs/codata-elaborator-design.md`).
