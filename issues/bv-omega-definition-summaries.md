---
title: bv_omega proves a summary lemma per definition instead of unfolding it at every use
status: open
labels: [performance,proofs,bitvec,metaprogramming]
area: tactics
created: 2026-09-27
updated: 2026-09-27
---

`bv_omega` steps through a definition (`double`, `times256`) by unfolding it
at each use (docs/tactics/bv-omega-design.md §2, "a definition"). So its cost grows
with the *unfolded* size of a word, not the number of definitions in it.
`raise(n)` is five `times256`, each eight `double`s: `raise_value` takes 40
`add`s apart and is the heaviest row left in `lib/decimal_line.hthr` (see
[[bv-omega-check-cost]]'s 2026-09-27 log).

A hand proof avoids this by proving a lemma per layer (`double_value`, then
`times256_value`, then `raise_value`), each used several times. The tactic
should do the same automatically.

## Shape of a fix

When the walk steps into a non-recursive definition `f(a₁ … aₖ)` whose body is
arithmetic over its parameters, prove a **summary** once. The summary is
`f`'s fact generalised over its arguments' forms, with the side conditions as
hypotheses stated over those forms, in the spirit of `add_form` and
`sub_form`. It is lifted into a lemma of its own, and every use instantiates
it. With summaries, `raise` costs one summary per definition (`double`,
`times256`, `raise`) plus five and eight instantiations, and never takes apart
40 `add`s.

Questions to settle first:

- **Where a summary lives.** Per declaration (a goal-arena slot, like
  `omega`'s atom list) is simplest. Per module, cached by definition key,
  would reuse across declarations, but the lemma would have to be a
  declaration that module images carry.
- **What a summary generalises over.** Argument forms with symbolic
  coefficients are not linear, since a form times a literal scale is.
  Simplest is to generalise over each argument's *value* (`toNat(aᵢ) = vᵢ`
  as hypotheses). Then the summary is a lemma over Nat variables, and the
  caller supplies each argument's fact.
- **Side conditions.** Their shape depends on the body. `double`'s is
  `v + v < 2^64`. They are stated over the `vᵢ` and discharged at each use,
  where they may compose into a single `omega` call.

## Acceptance

- `raise_value`'s check time scales with the number of definitions, not with
  their unfolded size. A probe of `raise` at three and at five `times256`
  layers shows the per-layer increment flat.
- Stating a sub-word's value by hand before `bv_omega` stops being needed
  for speed (the `line_state_start_value` trap in [[bv-omega-check-cost]]).
- No regression on the rest of `bv_omega`'s fixture
  (`perf/fixtures/bv_omega/`).

## What it assumes from elsewhere

- **[[bv-omega-check-cost]]** owns the per-call costs (omega context width,
  generalised words, facts shared between calls). Assumed here: only that a
  summary's instantiation costs less than the unfolding it replaces.

## Log

- 2026-11-05: gardener: cites a file it shares with [[certifying-arithmetic-proof-automation]] (`docs/tactics/bv-omega-design.md`).
