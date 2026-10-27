---
title: Summation methods with tracked laws: a series is not its sum
status: open
labels: [stdlib,mathematics,analysis,design]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

`docs/analysis-foundations-design.md` §3.8: a series is a formal object, and
a sum is a separate, partial operation whose laws are tracked. This issue
owns the summation-method interface and the theorems that make divergent
series ordinary working material.

Scope:

- the interface: a domain predicate on series, a value in an ordered
  field, and capability laws in Hardy's sense (regular, linear, stable,
  multiplicative, differential) as separate, optional evidence;
- the transfer theorem: a formal identity among series in the domain,
  plus the capabilities its operations need, gives the identity of the
  sums;
- instances: ordinary convergence (from [[power-series-evaluation]]),
  Cesàro and Abel;
- theorems over any linear stable method that sums them: `1 + 2 + 4 + …`
  gives `−1`, and Grandi's series gives `½`;
- the ¬ theorem: no linear stable method sums `1 + 2 + 3 + …`. Optionally,
  state what zeta regularisation keeps (linearity) and loses (stability).

## What it assumes from elsewhere
- **[[formal-power-series]]**: series as formal objects.
- **[[asymptotic-relations]]**: limits, for regularity.
