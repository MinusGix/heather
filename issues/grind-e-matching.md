---
title: grind: instantiate equations under binders by e-matching, and report the hints used
status: open
labels: [tactics,metaprogramming]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

Round 2 of [[grind-port]] (`docs/grind-design.md` §6): equations under
binders, from the goal's locals and from a hint list, instantiated by
matching their patterns against the graph's terms modulo its classes
(e-matching). Round 1 reads such an equation only at an instance written
as a hint (`grind_with([k(a)])`) and reports the others as "an equation
under binders, not read".

Wanted:

- A hint may be a lemma with binders (`List::append_assoc`,
  `List::append_nil`), by name or as a local of the goal.
- Its pattern is its equation's left side (both sides when one side alone
  does not bind every variable); a match is found against every node of the
  graph, comparing subterms by class, and each new instance is added as an
  equation and the graph closed again, up to a round budget.
- The used subset comes back: on success the tactic reports which hints its
  proof cites ([[lemma-selection-and-search]] piece 3). Today a tactic can
  only report on failure; this needs a host request that records notes
  without ending the run.
- On failure, the stuck state lists the patterns that never matched and the
  instances that were added.

Done when `grind_with` closes an append tower (`elf64`-style `trans`/`cong`
chains, [[monoid-normalisation]]'s examples) from the lemmas by name with no
instance written, and says which ones it used.

## What it assumes from elsewhere
- **[[grind-port]]** owns the graph and its proof reconstruction. Assumed
  here: only that an instance is one more equation with a proof.
- **[[lemma-selection-and-search]]** owns the hint-pool selection language.
  Assumed here: only that a hint list can be given.
