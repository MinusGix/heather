---
title: grind: read a stuck side one definition unfolding at a time, as the hand trans chain does by conversion
status: closed
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-08
updated: 2026-11-08
---

grind closes a proof when every step is an equation the graph can see. The
library's hand `trans` chains also cross steps that only conversion sees, and
grind does not take those steps. The native library is where most of the
hand chains are (`lib/native` holds most of the files with the most
`trans`/`cong_fn` calls), and most of those chains cross such a step.

Probe (2026-11-08, master `5df757c`): `rt_loop`'s `Fun::post_left`, whose
hand proof is four `trans` steps over `branch_false`,
`Valuation::set_here` and `Valuation::set_other`.

- With all four instances written as locals, `grind_report([], [])` stops
  one equation short. The goal's left side
  `loop_finish(Fun::post(x, rr, o0, exhausted), …)(LoopEnd(…))` is in a
  class by itself, and `branch(x, …).eval(call, q)(64, rr)` is in the class
  that the instances build. The two terms are the same up to δβ (unfold
  `loop_finish`, then `Fun::post`). Likewise `word_value(s0)(64)` and `s0`
  are in different classes but are equal by evaluation.
- Add those two equations as `refl` locals and the same call closes.
- The read-over-write core on its own,
  `Valuation::set(Valuation::set(v, y, b), x, a)(64, y) = b(64)` from
  `ne: y ≠ x`, closes by name
  (`grind_report(["Valuation::set_here", "Valuation::set_other"], [])`).

So the steps that are missing are the ones the hand chain gets free: `trans`
checks its middle term up to conversion.

The side reducts of §14.4 (`docs/tactics/grind-design.md`) read a side's head normal
form, and only when it is a constructor value. That is too far for this
case: the whnf of `loop_finish(…)(…)` runs past `branch(…).eval(…)` into
`eval`'s match. What would close it is reading a stuck side **one δ step at
a time**. Unfold a defined head (`loop_finish`, `Fun::post`) and β-reduce,
and give each intermediate application its own node, joined to the term as
written by a `defn` edge. Stop at the first spelling that a lemma's pattern
or another node meets. Evaluation of a closed or nearly closed value
(`word_value(s0)(64)` to `s0`) is the same step with the head unfolded into
a match on a literal.

Open questions: which heads to unfold (every transparent `fn`, or only
those under the goal's sides, bounded by a depth); how this meets
interface definitions (a withheld body is never unfolded, which is the
point of [[interface-definitions]]); and the cost, since each step is a
`Whnf`-like host request and one more node.

Done when `Fun::post_left` closes by `grind_using` with the three lemmas
its hand proof cites and no instance or unfolding written, and a negative
control shows that an `interface fn` head is not unfolded.

## What it assumes from elsewhere
- **[[grind-reduct-fields]]** owns how reduct fields are spelled. Assumed
  here: only that a reduct node is joined to its source by an edge the
  proof can cite.
- **[[grind-matching-fuel-on-native-terms]]**: the same probe with the
  lemmas given by name runs out of fuel before this question is reached.

## Log
- 2026-11-08: Done (docs/tactics/grind-design.md §15.1). A `Spell` host request
  returns a term's next spelling (head definition unfolded, head reduced
  until a call or a local is at the head again), through the interface
  boundary as conversion sees it. grind spells the stuck terms under the
  sides when they stay apart, joining each to its term by a `defn` edge,
  with stand-ins for premises and disequality premises from either
  orientation. `Fun::post_left` closes by `grind_using` with its three
  lemmas (`lib/_tests/std/tactic/grind_native_tests.hthr`), and
  `interface_head_folded` there is the negative control (`Interval::neg` at
  open arguments). The open questions: every stuck head under the sides,
  capped (`grind_spell_cap`, `grind_spell_passes`); a withheld body is not
  unfolded; each step is one host request and one node.
