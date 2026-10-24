---
title: Indexed families with infinitary premises (logical relations)
status: open
labels: [inductives,indexed-families,design]
area: language
milestone: [math-metatheory]
created: 2026-10-24
updated: 2026-10-24
---

A logical relation in logrel-coq's style is an indexed family with
infinitary premises. heather-coq's `LR` (`theories/LogRel/Def.v`) has, in
its Π, Σ and W cases and its modal cases, premises quantified over Kripke
worlds (`∀ ρ : kwk G Γ, LR … (domR ρ)`). Its index includes the term
relation, so the family is large too. Heather covers neither shape in
combination:

- `IWf` is finitary: its children are a `DVec` of a computed length.
- Tier 2 (`docs/inductive-tier2-w-lowering.md`) is infinitary but
  unindexed, with at most one recursive function field.

Options, from `docs/heather-coq-port-assessment.md` §4.2:

1. Indexed `W` as a kernel former. This needs a former round, with
   heather-coq checking it first, as `IWf` had M17.
2. A tier-2 lowering for indexed families: `W` plus an index
   well-formedness predicate. This needs no kernel change, and no funext
   while derivations are only eliminated.
3. A finitary redesign of the relation (store one derivation and prove that
   weakening preserves it). This is a research question, best probed in
   heather-coq.

Option 2 is the recommended first probe. The customer is
[[heather-coq-port]]'s third rung (a relation with no universe), which is
`math-metatheory`'s "done when".

## Log

- 2026-10-24: Filed from the heather-coq port assessment.
