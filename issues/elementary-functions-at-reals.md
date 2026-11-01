---
title: exp, sin, cos at real arguments, and their laws
status: closed
labels: [reals]
area: mathematics
created: 2026-10-27
updated: 2026-11-01
---

`CReal::exp_rat`, `sin_rat`, `cos_rat` (`lib/std/num/float/elementary.hthr`)
are defined at rational arguments only, and none of their laws is proved:
the probes show `sin(1)² + cos(1)² < 1.001` by enclosures, not `≈ 1`.

Scope:

- the functions at a real argument: either the series with real terms
  (a `CReal` version of `Series`, whose limit is `CReal::lim`), or the
  rational function extended by a modulus of continuity on bounded sets;
  the second keeps the enclosures as they are, read at an enclosure of the
  argument;
- the laws: `exp(a + b) ≈ exp(a) · exp(b)` (Cauchy product of the two
  series, or uniqueness of the solution of `f' = f` once
  `real-functions-and-derivatives` lands), `sin² + cos² ≈ 1`, the addition
  formulas, monotonicity of `exp`;
- an `Enclosed` leaf at real arguments, so `by intervals()` reads
  `exp(x)` for any real `x` it can enclose.

## What it assumes from elsewhere
- **[[interval-elementary-functions]]** (closed) owns the rational case.
- **[[real-functions-and-derivatives]]** owns continuity and derivatives at
  `CReal`, which one route to the laws goes through.

## Log

- 2026-10-27: docs/analysis-foundations-design.md §8 proposes the laws as formal identities proved by coinduction over Hurwitz series ([[formal-power-series]], §3.4) carried through evaluation as a ring homomorphism ([[power-series-evaluation]]); no real derivatives needed.
- 2026-10-31: 2026-10-31: `CReal::log_rat` exists (lib/std/num/float/elementary.hthr, the atanh series after scaling into one binade, plus e·log 2), defined as that sum: `exp(log q) ≈ q` and `log(exp a) ≈ a` are owed here with the other laws ([[creal-compress-and-transcendentals]]).
- 2026-10-31: exp-log-grid-gap closed for exp (2026-10-31, lib/std/num/float/pade.hthr). log's gap is now [[log-grid-gap]], blocked here: it needs exp(log q) ≈ q and exp monotone or Lipschitz on a bounded interval at real arguments.
- 2026-10-31: `CReal::sqrt` exists at real arguments (creal.hthr; [[float-reals-next]]): terms are the rational function at a finer term of the argument, regular by a modulus of continuity (Hölder-½, `Rat::lt_root_floor_add`), with the law `√x·√x ≈ |x|` proved through the cut. The same template is the second route above.
- 2026-10-31: exp is done at real arguments, with its laws (thread "Define exp, sin and cos at the reals"). The route is the issue's second one, with the laws first proved at rationals:

  - `lib/std/num/float/exp_law.hthr`: exp(a + b) ≈ exp(a)·exp(b) at rationals, as a Cauchy product. The coefficient identity `Σ_{i+k=n} a^i/i!·b^k/k! = (a+b)^n/n!` is proved by splitting the weight n+1 as i + (n+1-i), so no binomial coefficients are needed (`Series::exp_prod_term_eq`). The limit is a generic theorem for `Series` with majorants (`Series::cauchy`: the square of partial sums less the triangle is bounded by the majorants' square less their triangle, which lies inside their triangle of side 2N). From the law: `exp_rat_pos`, `exp_rat_le`/`exp_rat_lt`, `exp_rat_bound`, and the Lipschitz bound on [-B, B] (`exp_rat_lip`, constant `exp_lip(B)`), through `Series::drop` (a series from its j-th term) for exp(d) - 1.
  - `lib/std/num/creal_lipschitz.hthr`: `RatLip`, a rational-argument function with a Lipschitz bound on every bounded set, extended to `CReal` by `CReal::lim` (`RatLip::ext`), with the one estimate `ext_dev` (a real within e of a rational q has its image within lip·e of f(q)), `ext_ofRat` and `ext_respects`.
  - `lib/std/num/float/elementary_real.hthr`: `CReal::exp`, with `exp_ofRat`, `exp_respects`, `exp_add`, `exp_neg_mul`, `exp_le`, `exp_lt`, `exp_pos`, `exp_dev`, and the checker leaf `exp_real_box`, which `by intervals()` reads at `CReal::exp(x)` for any real x (probes in lib/_tests/std/num/float/elementary_real_tests.hthr).

  Still owed here: sin and cos at real arguments, and their laws (the addition formulas and sin² + cos² ≈ 1), next in the same thread; and `exp(log q) ≈ q`. The last is not cheap: log is 2·atanh(t) + e·log 2, and exp(e·log 2) = 2^e follows from `exp_add`, but exp(2·atanh t) = (1+t)/(1-t) needs either derivatives with ODE uniqueness ([[real-functions-and-derivatives]]) or composition of power series ([[formal-power-series]], [[power-series-evaluation]]).
- 2026-11-01: sin and cos are done at real arguments, with their laws (thread "Define exp, sin and cos at the reals", second PR), so the scope is complete:

    - `lib/std/num/float/trig_law.hthr` proves the addition laws at rationals, `CReal::sin_rat_add` and `cos_rat_add`. sin's and cos's series are exp's at odd and even places, signed by σ = 0, 1, 0, -1, … and γ = 1, 0, -1, 0, …, and these signs obey the addition formulas themselves (`Series::pattern_add`). With exp's coefficient identity, each degree's coefficient splits over the antidiagonal (`Series::sin_prod_term`, `cos_prod_term`). The Cauchy product is now stated over term functions (`Rat::cauchy_gap`, `Rat::cauchy_square`, exp_law.hthr), and `CReal::cauchy2_near` closes two products against one partial sum. The file also has:
      - parity (`sin_rat_neg`, `cos_rat_neg`);
      - small-argument bounds (`sin_rat_small`, `cos_rat_sub_one`);
      - one Lipschitz modulus for both, `CReal::trig_lip`, from the addition laws.
    - `RatLip::ext_odd` and `ext_even` (creal_lipschitz.hthr) carry parity to the reals.
    - `lib/std/num/float/elementary_real.hthr` adds `CReal::sin` and `CReal::cos`, with `sin_add`, `cos_add`, `sin_neg`, `cos_neg`, `sin_sq_add_cos_sq` (sin² + cos² ≈ 1) and `sin_dev`/`cos_dev`. Their checker leaves, `sin_real_box` and `cos_real_box`, are the rational enclosure at the argument's n-th term, padded by the Lipschitz bound. The pad is computed in dyadics from exp's enclosures, because the exact `trig_lip` rationals run out of kernel fuel. The pad still grows with the argument's bound: a real near 10 already runs out. A tighter leaf would use the addition law at the term, with |sin|, |cos| <= 1, or argument reduction ([[interval-log-and-reduction]]).

  `exp(log q) ≈ q` moves to [[exp-log-inverse]].
