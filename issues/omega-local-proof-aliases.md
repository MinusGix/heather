---
title: Let Omega consume explicitly named local proof aliases
status: open
labels: [tactics,omega,ergonomics]
created: 2026-09-05
updated: 2026-09-05
---

The positive-subtype probe in `docs/showcase/positive_omega.hthr` establishes
that Omega can prove `0 < x.value + y.value` given a parameter
`positive: 0 < x.value`. However this body gets stuck:

```heather
theorem closure(x, y: PositiveNat): 0 < x.value + y.value {
    let positive = x.valid;
    omega
}
```

The diagnostic lists atoms `x.value`, `y.value`, their nonnegativity, and the
negated goal, but does not include the named positivity alias. The current
working bridge is `projected_sum_positive(x, y, x.valid)`, where the helper has
that proof as an ordinary parameter and its entire body is `omega`.

## Acceptance

- Make explicitly named proof aliases available to Omega with correct scope,
  shadowing, and dependency handling. Do not scan arbitrary record fields or
  assume a field named `valid` has a particular meaning.
- Check the sum-positive example and a refusal control with insufficient or
  irrelevant evidence; preserve kernel-checked reconstruction.
- Distinguish this fact-collection step from a general positivity tactic.
  Nonlinear closure lemmas and domain-specific preservation rules remain a
  separate solver-composition question under [[setoid-auto-lifting]].

Related: [[omega-linear-arithmetic]], [[subtype-transfer-and-evidence]].
