---
title: Evaluate power series at reals as a ring homomorphism
status: open
labels: [stdlib,mathematics,analysis,reals]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

Layer E of `docs/analysis-foundations-design.md` (§8): series as range sums
with a tail modulus, power series with a Cauchy majorant evaluated at `CReal`,
and evaluation as a ring homomorphism on the disc of convergence.

Scope:

- convergence by comparison with a majorant, with explicit rates, limit via
  `CReal::lim`;
- `PowerSeries<Rat>` with `|a_n| <= M / r^n` (rational `M`, `r`), evaluated at
  `|x| <= r' < r`; the Cauchy product theorem at majorants; evaluation
  respects `+` and `*`;
- `exp`, `sin`, `cos` at real arguments as evaluations of the formal series,
  with their laws carried from the formal identities;
- rebase `Series::sum`/`tail`/`decay` onto the range sum and geometric lemmas,
  changing no statement `elementary.hthr` exports.

The first divergent-expansion customer after this is
[[harmonic-and-stirling-asymptotics]].

## What it assumes from elsewhere
- **[[formal-power-series]]**: the formal laws.
- **[[asymptotic-relations]]**: `Tendsto` at `n → ∞`.
- **[[elementary-functions-at-reals]]** owns the elementary functions' API;
  this issue supplies the route to their laws.
