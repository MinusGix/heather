---
title: A cast-pushing step that moves embeddings (Dyadic::rat, CReal::ofRat, …) through arithmetic along ≈
status: open
labels: [tactics,rewriting,reals,intervals]
area: tactics
created: 2026-10-30
updated: 2026-10-30
---

Bounds in the float and interval libraries live in one carrier and are
compared in another: a `Dyadic` bound is read as `d.rat()`, a `Rat` one as
`CReal::ofRat(q)`, an `Int` one as `Rat::ofInt(n)`. Every step that does
arithmetic on bounds then owes a homomorphism law by hand, on the side it
happens on:

```heather
// interval.hthr before 2026-10-30
let low: ((a + c).rat() <= x + y) = Rat::le_respects(Rat::same_sym(a.rat_add(c)), (x + y).same_refl(), Rat::add_le_mono(hx.left, hy.left));
```

The 2026-10-30 round made this one call (`Interval::bnd_has_of(a.rat_add(c),
b.rat_add(d), …)`), but the caller still names `rat_add` and `rat_mul`
itself, and `creal_interval.hthr` does the same with `real_add`,
`real_mul`, `real_neg` (`Dyadic::real_*`). What Lean does here is
`push_cast`: a rewrite set, registered per embedding, that normalizes
`(a + c).rat()` to `a.rat() + c.rat()`, and that `gcongr` runs before it
compares the two sides.

Sketch:

- A registry like `mono`'s carrier table (`lib/std/tactic/mono.hthr`): per
  embedding `e: A → B`, the laws `e(a + b) ≈ e(a) + e(b)`, `e(a * b) ≈ …`,
  `e(-a) ≈ -e(a)`, `e(0) ≈ 0`, `e(1) ≈ 1`, and `a <= b ↔ e(a) <= e(b)`.
  `Dyadic::rat`, `CReal::ofRat`, `Rat::ofInt` are the first three.
- The step itself is setoid `rewrite` bottom-up along `≈`
  ([[rewrite-setoid-relations]]), which already crosses `+`/`*` by their
  `Respects2` instances; this issue adds only the law set and the
  direction (images outward → images at the leaves).
- `mono` calls it on both sides before `mono_same`, so the containment
  bound above is `<= x + y := by mono_with([hx.left, hy.left])`.

Customers: `interval.hthr` (`add_bnd_has`, `mul_pos_has`, `neg_has`,
`corner_lo/hi`), `creal_interval.hthr`'s `_real` copies, `dyadic.hthr`'s own
order lemmas (`Dyadic::neg_le`, `rat_pos`, …, each a `Rat` lemma between two
image laws), and the `Dyadic::Le`-typed facts that need their implicits
named at every `Rat::le_trans` (`widen_has`).

## What it assumes from elsewhere

- **[[rewrite-setoid-relations]]** owns `rewrite` along a relation.
  Assumed here: only that it rewrites bottom-up under `+`/`*` given their
  `Respects2` instances.
- **[[monotonicity-tactic]]** owns `mono`. Assumed here: only that a
  preprocessing step on the goal's two sides can run before its comparison.
