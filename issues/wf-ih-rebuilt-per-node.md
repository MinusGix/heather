---
title: elim_Wf rebuilt its induction hypothesis's syntax at every node
status: closed
labels: [performance,kernel,evaluator,inductives]
created: 2026-09-26
updated: 2026-09-26
---

Every `elim_Wf` β built its induction hypothesis
`λ i. elim_Wf(e; nth(Wf; n[a/x]; cs; i))` as syntax
(`Eval::fire_elim_wf`), which shifts the eliminator's shape, arity, motive
and *whole step body* under three binders. The recursive call then carries
that shifted copy, so the next β shifts it again: each node of a structural
recursion over a `List` or a tree allocated a fresh copy of the recursor.
Because `TmClo::ident` keys memos on the body's syntax pointer, no memo keyed
on syntax identity (the conversion memo, the `Nat` fold-class memo) could hit
across nodes either.

## Attribution

Found by remeasuring after [[nominal-tag-conversion-cost]]: omega's
`sub_coeffs(la, lb) = lc` by `refl` cost about 0.55 ms and 157 kernel steps
per element, about 3.6 µs per step against about 0.4 µs for a plain list
comparison. A frame-pointer profile put about 30% of samples in `ShiftLocal`
under the evaluator and 7.7% in `term::nth`. Timing the ih construction alone
(temporary counters, not kept): 27 of 51 ms of gate at 100 elements, 95 of
221 ms at 400, about 60 µs per β, before the cost of evaluating the shifted
syntax.

## Fix

`Val::WfIh { elim, label, children }` holds the ih natively. Applied to a
canonical `Fin` index over a canonical pair chain, it selects the child
(`inl _` the head, `inr j` the `j`th of the tail, which is what `nth`
reduces to) and fires the original eliminator on it, one fuel unit per
projection. A neutral index, a stuck or glued tuple, and every reader that
inspects the function instead of applying it get the λ built exactly as
before (`Eval::wf_ih_lam`). This is a strategy change with no semantic
content: conversion treats the value as opaque and compares functions by
applying them, which lands on the same fallback. `crates/kernel/tests/wf.rs`
pins both fallbacks (a neutral tuple, a neutral index).

## Result

Probe (`sub_coeffs` refl, width 1): gate 17.1 → 1.3 ms at 25 elements,
53 → 6.6 ms at 100, 224 → 32 ms at 400 (−86 to −93%); kernel steps −11%.
The time was allocation and shifting, not reduction.

## Log

- 2026-09-26: LANDED. `scripts/perf ab --base HEAD` (3 interleaved cold samples, every headline row `separate`): the bv fixture's kernel gate −54.4% (wall −34.4%; `bv_place_step` 1.052 → 0.277 s, the `taken_*`/`kept_*` hand lemmas −73 to −81%); `lib/std/omega` gate −32.7%, wall −18.4%, max RSS −17%; `docs/showcase/calc_parser` gate −32.3%. eval_steps −3 to −5%: the same reductions, without the per-node syntax. One small separate regression, `calc_parser::close_body` 26 → 27 ms (+4.9%), not chased. Full suite green (3,002 passed). `scripts/bench --check`: `wf/mirror-involution` 0.39–0.41× at every size, slope unchanged; two flags not from this change — `code/check-identity-recursor:3` was noise (301 µs on rerun, within threshold), and `wf/check-tree`'s slope 0.79 is outside its 0.85–1.35 band at 60306512 too, before both of today's kernel commits (a stale band, left alone). Side finding while scaling the probe: [[nested-constructor-elaboration-stack-overflow]].
