---
title: induct on a runtime fn: case binders lose the test names, and case λs cannot see past the motive
status: closed
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

## Log

- 2026-11-24: 2026-11-24: Fixed (551817a). Cause: `if more: P` lowers to a convoy that
  binds `let more = decide_true<P>(…)` only in a branch that names `more`
  (parser.rs, the `if h:` lowering); `find_at`'s branches cite none of their
  tests, so nothing carried the names and the equations numbered them `h`,
  `h3`, …. Where neither branch names the evidence, the convoy's private
  equation is now `__if_bitN_more` (`heather_syntax::if_bit_unnamed`), and
  `branch_equations::Walk::hypothesis` and `measure::step_equations` take the
  written name from it (`if_bit_written`); the function's term is unchanged.
  Not `runtime fn`-specific: a plain `fn` whose branches never cite their
  tests lost them too, so a loop route that defines a tail-recursive
  `runtime fn` differently keeps the names as long as its principle is read
  off the written `if h:` (docs/language/loop-combinator-design.md §6.5).

  Item 2 (untyped binders past the motive) did not reproduce with the names
  fixed: `T::scan_by_hand_record` and `T::scan_by_hand_defined` apply the
  principle by hand with a case λ whose binder past `motive(j, left)` is read
  as a record (`p.left`), the motive's body a literal Π and a defined
  proposition. Probe: lib/_tests/native/runtime/runtime_induct_names_tests.hthr.
  `word_map_laws.hthr`'s seven probes are `induct` arms now (0a6a79c).
- 2026-11-24: 2026-11-24: The name now travels as data, per Minus (less magic, more explicit structure): `ExprKind::Match::test` holds the name an `if h:` gave its test, on the match it lowers to; the branch equations, f::step and f::induct read it, every pass that rebuilds a match carries it, and module images store it (format bumped, HTHMOD 0x28 / HTHIFC 0x22). The `__if_bitN_more` encoding is gone. Nothing that computes a term reads the field. New probe pair induct_names_source_tests / induct_names_import_tests: an imported structural recursion whose `if big:` no branch cites, with induct arms citing `big` over the replayed image, and a negative control.
