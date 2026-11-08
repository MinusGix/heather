---
title: omega reads Nat and Int max/min by their two cases instead of as atoms
status: open
labels: [tactics,omega,arithmetic]
area: tactics
milestone: [tac-arith]
created: 2026-11-08
updated: 2026-11-08
---

`omega` treats `a.max(b)` as an opaque atom:

```heather
theorem m_le(a, b, c: Nat, h1: a <= c, h2: b <= c): a.max(b) <= c { omega }
// `omega` got stuck: … CutSat's integer model [a = 0, c = 0, b = 0,
// nat::Nat::max(a, b) = 1]; atoms [a, c, b, nat::Nat::max(a, b)]
```

So every proof that picks an index past two thresholds carries the max
lemmas by hand: `p.witness.le_max_l(q.witness)`, `.le_max_r`, then
`le_trans` to the later index (lib/std/analysis/sequence.hthr's
`Converges::le`, `squeeze`, and their kin; 80 calls to `le_max_*`,
`max_le`, `le_min`, `min_le_*` across lib/std). Lean's `omega` handles
`min`/`max` (and `if`) by adding the two defining facts per atom; the same
works here.

## Direction

When reifying, an atom `max(a, b)` (and `min`) at `Nat` or `Int` with linear
arguments gets the facts `a <= m`, `b <= m`, `m = a ∨ m = b` (dually for
`min`), the disjunction handled by the case split omega already does for
`¬(x = y)`-style facts. The facts come from `Nat::le_max_l`, `le_max_r` and
a `max_cases` lemma in nat.hthr/int.hthr, so the certificate cites theorems,
never unfolds `max` (whose definition is a recursion).

## Acceptance

- `m_le` above checks, and `Converges::le` in sequence.hthr can drop its
  `le_max_*` calls.
- Int: `a.max(b) >= a + 0` and a goal mixing `min` and `-`.
- Control: a false goal (`a.max(b) <= a`) still fails with a model.
- Cost: `scripts/timings --diff` on omega_tests shows no new atoms or
  certificate growth on goals that mention no `max`/`min`.

Related: [[cutsat-first-class-relations]]; docs/stdlib-math-awkwardness-survey.md §8.
