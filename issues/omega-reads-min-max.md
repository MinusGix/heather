---
title: omega reads Nat and Int max/min by their two cases instead of as atoms
status: closed
labels: [tactics,omega,arithmetic]
area: tactics
milestone: [tac-arith]
created: 2026-11-08
updated: 2026-11-09
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

## Landed (2026-11-09)

`omega` splits a `max`/`min` read at `Nat` or `Int` by the order of its
arguments (`split_max_min`, the last fallback of the attempt that answers):
`omega::nat_max_elim` and its three siblings in omega.hthr give `a <= b`
with the read equal to `b` (`max`) or `a` (`min`), or `b <= a` with the
other, each branch closed by `omega` again. The lemmas cite
`max_eq_l`/`max_eq_r`/`min_eq_l`/`min_eq_r` (nat.hthr gains
`Nat::max_eq_l`), never the definitions. A case split rather than the three
facts with a disjunction: the case's two facts imply all three, and the
split is the shape §16's subtraction split already takes. Design:
`docs/omega-measure-reduction-design.md` §20.

Probes in `lib/_tests/std/tactic/omega_tests.hthr`: `max_le_bare` (this
issue's `m_le`), `le_min_bare`, `max_bounds`, `min_add_max`,
`max_in_fact`, `max_nested`, `max_of_sub`, `int_max_ge`
(`a + 0 <= a.max(b)`), `int_min_sub` (`min` with `-`), `int_max_neg_min`,
and the refused controls `max_le_left` and `int_min_ge_left`, whose reports
name `__omega_mm0_case`. Goals with no `max`/`min` are untouched by
construction: the split is reached only after CutSat found a model.

`Converges::le`, `unique`, `add` and `squeeze` (sequence.hthr) now pass
`omega` for the index; `Converges::mul` keeps its chain because omega cannot
spell its witnesses (projections through the ordered-field dictionary). The
rest of the library is [[omega-max-min-sweep]].
