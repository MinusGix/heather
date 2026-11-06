---
title: Make grind_report name the hints its search needed, not only the ones its proof cites
status: closed
labels: [tactics, grind]
area: tactics
milestone: [tac-general]
created: 2026-11-06
updated: 2026-11-06
---

`grind_report` named the hints the explanation path cites (`cited_alg`) and
called every other hint "not used". A hint can be needed without being
cited: its instance, or its equation as read, puts a term in the graph that
a cited lemma's near match then draws its binder from, or finds its hole's
solution among (docs/grind-design.md §13.1, §13.4). The proof cites the
matched lemma, not the hint that supplied the term, so narrowing the call
to the report's list, which is the report's stated job (§9.4) and the plan
of [[lemma-selection-and-search]] §3, breaks the proof.

This is the *lurking axiom* of Gopinathan et al., "Accelerating Automated
Program Verifiers by Automatic Proof Localization" (CAV 2025, the Axolocl
tool): an SMT axiom outside the UNSAT core whose instances produced the
ground terms that triggered a core axiom. Their fix walks Z3's
instantiation graph back from each core axiom; grind's is the same walk,
kept as provenance on the graph's nodes.

Found probe (master 7ce3115): `lurk_one: Nat::add(1, 0) = 1` is the only
source of the node `1`, which `lurk_sc(?b) ≡ lurk_two()` needs as `?b`;
`grind_report(["lurk_one"], [])` closes `c(lurk_two()) = 0` from
`k: (b: Nat) → c(lurk_sc(b)) = 0` and said "not used: lurk_one", and
`grind_report([], [])` fails.

## Done when

- Each node records which facts brought it into the graph, closed under the
  terms an instance was matched at; the report names a hint whose terms the
  proof stands on but does not cite separately ("not cited, but needed to
  find it").
- `lib/_tests/std/tactic/grind_tests.hthr` holds the probe and the narrowed
  control.

## What it assumes from elsewhere

- **[[grind-near-match-new-terms]]** owns interning a solution that is no
  node. Assumed here: only that a solution today must already be a node,
  which is what makes a term's source matter.

## Log

- 2026-11-06: Filed and done in one round. `GInfo.by` per node, `Fact.found`
  per edge and `found_alg` over the explanation path, docs/grind-design.md
  §9.6. The probe reports `not cited, but needed to find it: lurk_one`; the
  library's other reports are unchanged.
