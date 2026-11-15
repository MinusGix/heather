---
title: grind: instantiate lemmas with premises, proving each premise at the instance
status: closed
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

## Log

- 2026-11-02: Done (docs/tactics/grind-design.md §11). A binder no side binds and nothing depends on (`Open`'s flag) is a premise, proved at each instance in order: an equation by the graph (sides read in, graph closed, the explanation), any premise by a local or a hint that is no equation (`Defeq`; non-equation hints are now kept for premises rather than "not read"), or by `Synth`. An instance whose premise is not proved is pending and retried after each round that adds instances; the failure lists pending instances by the premise each lacks. Probes in lib/_tests/std/tactic/grind_tests.hthr: `premise_local` (`<` by a local), `premise_graph` (equation by the graph, no local is it), `premise_synth`, `premise_later` (waits a round), `premise_hint`, `set_set_hit_other`, `premise_reported`, `premise_unproved` (the report names `k, premise 1`) and `premise_exists` (refused). A premise tactic (`grind_by`) was prototyped and left out: [[grind-premise-tactic]].
