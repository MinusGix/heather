---
title: Spell one-sided ≈ steps with le_of_same_of_le / le_of_le_of_same, not le_respects(…, same_refl(), …)
status: open
labels: [stdlib,cleanup,reals]
area: mathematics
created: 2026-10-30
updated: 2026-10-30
---

`Rat::le_respects(hx, hy, h)` moves both sides of a `≤` along `≈`. Most
uses move one: about 120 calls in `lib/` pass `X.same_refl()` for the side
that stays, often with `Rat::same_sym` on the other because the image law
points the other way:

```heather
Rat::le_respects(Rat::same_sym(a.rat_mul(c)), s.same_refl(), l)   // (a*c).rat() <= s
Rat::le_of_same_of_le(a.rat_mul(c), l)                            // same, 2026-10-30
```

`Rat::le_of_same_of_le(x ≈ y, y <= z): x <= z` and
`Rat::le_of_le_of_same(x <= y, y ≈ z): x <= z` landed with the interval
round (2026-10-30, `rat.hthr`); `interval.hthr` uses them. Left:

- the other ~110 `Rat` sites (`round.hthr` has 62 `le_respects` calls,
  `error.hthr` and `window.hthr` 20 each, `creal_interval.hthr` 15);
- the `<` pair (`lt_of_same_of_lt`, `lt_of_lt_of_same`) and the same four
  at `CReal` (`creal.hthr`), with `CReal`'s sites;
- whether a two-step `calc` reads better than either at a given site (a
  chain of three or more steps does).

Mechanical, but each site is a judgment call between the lemma and a
`calc`; do it by file, not by regex. [[push-cast-through-embeddings]] would
remove the image-law half of many of these sites outright.
