---
title: grind: instantiate lemmas with premises, proving each premise at the instance
status: open
labels: [tactics,metaprogramming]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

Round 2 of [[grind-port]] ([[grind-e-matching]]) sets aside a lemma one of
whose binders neither side of its equation mentions: a premise
(`(i: Nat) → i < xs.len() → …`, `n ≠ 0 → …`). Most library lemmas worth
handing grind carry one, so this is likely the main gap between grind and
the library's hand `trans`/`cong` chains; [[grind-library-sweep]] measures it.

Wanted: a lemma with premises is matched on the binders its sides bind, and
each premise is then proved at the instance, in order:

- an equation premise (`a = b`): by the graph, if its sides are in one class
  (explained like the goal);
- any premise: by a local whose type it is (`Defeq`), or by `Synth` (the
  `:= infer` search, facts-on-demand's evidence rules);
- otherwise the instance is not added, and the failure report says which
  premise of which instance was not proved.

A premise that mentions a binder no side binds (`∃`-like) stays refused.
The kernel checks the whole proof, so a wrong premise proof is a refusal at
the `by`, never an unsound graph.

Done when a lemma with a `<` premise discharged by a local and one with an
equation premise discharged by the graph both close, and the report names
an unproved premise.

## What it assumes from elsewhere
- **[[grind-e-matching]]** owns the matching and the rounds. Assumed here:
  only that an instance is a lemma applied to the matched terms.
- **[[facts-on-demand]]**-style `Synth` answers the non-equation premises.
