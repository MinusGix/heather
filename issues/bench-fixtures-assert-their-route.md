---
title: A fixture asserts the route the classifier picks, or it can measure the wrong scheme for rounds
status: closed
labels: [testing, tooling, elaboration, inductives]
created: 2026-08-06
updated: 2026-08-09
---

`forded/declared-index-tags` measured the wrong scheme for two rounds: its
name and doc claimed forded, `classify_indexed_route` picks route 1 (pattern
indices, tried first), and no test crossed the claim with the classifier.
Two rounds of forded levers "inexplicably" failed to move it, a third defect
was hypothesized from machinery the declaration does not emit
([[wf-shape-annotation-slots]], since corrected), and route 1's lever moved
it at once — 2.79 → 2.22 (`docs/frontend-benchmarking.md`, 2026-08-06,
"name the route the classifier picks, not the route the source looks like").

The discipline that would have caught it on day one is one assertion:
**every fixture whose point is a lowering scheme asserts which scheme the
classifier actually picks**, next to the source string. A fixture that
drifts routes — because the classifier's order changed, a new route widened,
or the source never was what its name said — then fails loudly instead of
quietly measuring something else.

Scope when a round takes it:

- Bench families in `crates/elab/benches/frontend/fixtures/` that sweep a
  lowering (the forded and indexed files): a classification assertion per
  family, checked once at the family's smallest size (cheap; the sweep
  itself stays unchanged).
- The generated-term test fixtures whose *point* is a specific route
  (`indexed_route1.rs`, `indexed_route_2b_*.rs`, …): same one-liner where
  the route is load-bearing and not already pinned by a
  rejection-message assertion.
- `docs/testing-generated-terms.md` gains the rule — as axis 7 or as a
  standing note under the axes: *a test of scheme S first proves it is
  exercising S*. The doc's five-defects history is all "the test varied the
  wrong thing"; this is "the test measured the wrong subject", the same
  failure one level up.

Deliberately small; no design questions. The only judgment call is which
existing fixtures are route-load-bearing, and the 2026-08-06 misattribution
is the worked example of the cost of guessing wrong.

## What it assumes from elsewhere

- **[[indexed-families]]** owns the route classification
  (`classify_indexed_route`/`classify_forded`). Assumed here: only that a
  fixture can call it and name the answer.

## When

Triggered: the next round that adds or renames a swept lowering fixture, or
the next time a bench family's slope resists an explanation — assert the
route before hypothesizing a defect.

## Log

- 2026-08-06: Filed, off the `declared-index-tags` misattribution
  post-mortem ([[parallel-checking-and-caching]]'s filing discussion).
- 2026-08-09: LANDED: IndexedRoute and Elaborator::indexed_route expose only the classifier result; every route-sensitive frontend benchmark asserts its smallest generated case (including declared-index-tags as route 1), the route-1 and route-2b generator acceptance fixtures pin their claimed routes, and testing-generated-terms records axis 7. Targeted acceptance, both benchmark smoke families, and the full suite pass.
