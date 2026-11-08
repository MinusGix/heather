---
title: State the carriers' respects theorems as the evidence setoid rewrite looks for
status: open
labels: [setoids,stdlib,rewrite,reals]
area: mathematics
milestone: [tac-general]
created: 2026-11-08
updated: 2026-11-08
---

Setoid `rewrite` and `rel_cong` cross an operation by a `Respects2`
instance (binary) or an `evidence theorem` stating `PreservesRelation(R, S,
f)` (unary; crates/elab/src/rewrite/relation.rs). At `Rat` and `CReal` only
`+` and `*` have that evidence (`instance Respects2` in rat.hthr, creal.hthr,
dyadic.hthr). The rest exist as plain theorems, 35 of them at the two
carriers: `abs_respects`, `neg_respects`, `sub_respects`, `div_respects`,
`inv_respects`, `npow_respects`, `exp_respects`, `log_respects`,
`sqrt_respects`, `sin_respects`, `cos_respects`, `lim_respects`, …
(`grep -rhoE '^theorem (Rat|CReal)::[a-z_]*respects' lib/std`). So:

```heather
theorem g2(a, b, c: Rat, h1: a ≈ b, h2: b ≈ c): a.abs() + 1 ≈ c.abs() + 1 {
    rewrite(h1, rewrite(h2, (c.abs() + 1).same_refl()))
}
// unsolved goals: ?compatibility : PreservesRelation(Same, Same, abs)
```

and the library writes the congruence by hand instead:
`CReal::mul_respects(H.same_refl(), a)`, `Rat::abs_respects(Rat::sub_respects(
(x.at(a) * y.at(a)).same_refl(), …))`. The `same_trans`/`same_sym`/`respects`
family is about 3,100 occurrences across lib/std/algebra, analysis and num
(docs/stdlib-math-awkwardness-survey.md §3); this is the cheapest part of it
to remove.

## Direction

- Library, mechanical: an `evidence theorem` per unary respects theorem and
  a `Respects2` instance per binary one, at `Rat`, `CReal`, `Dyadic`, and
  the class operations in `ordered_field` (`K.inv`, `K.recip` at a fixed
  apartness).
- Better, so the next carrier cannot forget: let a respects theorem register
  itself. Either a `respects theorem` declaration form that states the
  theorem and its evidence in one go, or `rewrite` reading a theorem named
  `<op>_respects` at the operation's owner. The first is explicit and fits
  [[relational-certificate-registration]]; this issue only needs one of them.

## Acceptance

- `g2` above checks with no `on` clause, at `Rat` and at `CReal`.
- `real_log.hthr`'s `atanh_clamp_id` loses its hand congruences
  (`CReal::mul_respects(H.same_refl(), a)`) to rewrites, as the customer.
- A control: an operation that does not respect `≈` (`Rat::den`-reading) still
  leaves the compatibility goal open.

## Related

[[egraph-setoid-path-algebra]] (grind over `≈`; today grind reads `a ≈ b` at
`Rat` as its cross-multiplication equation and cannot close `|a| + 1 ≈ |c| +
1` from `a ≈ b ≈ c`), [[setoid-surface-kernel-cost]],
[[one-sided-respects-sweep]], [[setoid-auto-lifting]].
