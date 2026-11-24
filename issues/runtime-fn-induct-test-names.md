---
title: induct on a runtime fn: case binders lose the test names, and case λs cannot see past the motive
status: open
labels: [tactics,runtime]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

Found proving the word map's specification ([[runtime-hash-map-spec]]).
`WordMap::find_at` (a `runtime fn` over a laid record, `decreases
left.toNat()`, tests `if more: 0 < left`, `if lt: j < 4`,
`if empty: m.keys.at(j) = 0`, `else if hit: m.keys.at(j) = k`) has an
induction principle, but:

1. **Its case binders carry none of the source's test names.** In
   `induct WordMap::find_at(m, k, j, left) { True::True::True => … }` the
   names `more`, `lt`, `empty` are unbound; the principle's binders are
   `x`, `y`, `z`, `a`, `b`, `c`, `x8` (its type, printed by a mismatch). The
   design (docs/tactics/functional-induction-design.md §2) says an arm sees the
   tests "under the names the function gave them"; a plain `fn` copy of the
   same body does get them.
2. **Applying the principle by hand, a case λ's binders past the motive's
   β-redex get no types.** With the motive `λ (j: u64) (left: u64) => P(j,
   left) → … → goal`, a case `λ j left more lt empty eq j4 budget clear =>
   …` binds `clear` at an unknown type ("no field `left` here (and the
   receiver's type could not be inferred)"): the case type's
   `motive(j, left)` is not reduced to expose its Π. The proofs state each
   case as a lemma whose result is the motive's body
   (`WordMap::finds_empty`, `finds_hit`, `finds_next`) and pass
   `λ j left more lt empty eq => WordMap::finds_empty(…)` (every probe in
   `word_map_laws.hthr` is written so).

## Wanted

The principle's case binders named as the function's tests (and `h`, `eq`,
`ih` as elsewhere), so `induct`'s arms work for `runtime fn`s; and a case
λ checked against `motive(x̄)` with the β-redex reduced before its binders
are introduced.
