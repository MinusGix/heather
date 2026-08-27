---
title: Build complete certifying LIA with a shared arithmetic substrate and CutSat
status: open
labels: [proofs,elaboration,arithmetic,solver,design]
blocked-by: [omega-linear-arithmetic]
created: 2026-08-27
updated: 2026-08-27
---

Implement the staged design in
`docs/certifying-arithmetic-substrate-design.md`: keep Omega as the fast affine
first pass, extract its reusable reflection/certificate plumbing, and add a
model-based CutSat fallback for complete supported linear integer arithmetic.

The architectural goal is broader than closing Omega's current shadow gap.
CutSat should eventually provide incremental constraints, typed proof
justifications, candidate assignments, resource-limit state, and decision
dependencies that a future `grind` can consume. Future `linarith` and nonlinear
arithmetic share canonical arithmetic reflection and certificate construction,
not the integer-specific Cooper search.

## Acceptance

- Shared affine reflection retains Nat/Int embeddings, opaque-atom sharing,
  deterministic atom labels, checked coefficients, and all current Omega
  behavior.
- The search-only CutSat core classifies the generated 20,000-system rail and
  closes all 91 pinned real-shadow misses, including seed 680's minimized thin
  system and Pugh's nightmare.
- Cooper conflict derivations reconstruct through named Heather lemmas and the
  ordinary kernel gate, with reachable-node sharing and exact used-lemma audit.
- Equality, inequality, disequality, and divisibility constraints are supported
  explicitly; candidate models satisfy every supported reflected constraint.
- Step/resource exhaustion returns a partial model and structured residual
  state, never a satisfiability or contradiction verdict.
- The eventual tactic path tries Omega first and invokes CutSat only after a
  structured real-shadow survivor, with comparative telemetry.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** supplies the landed affine solver,
  reconstruction boundary, and reports from which the shared substrate is
  extracted.
- **[[omega-property-testing]]** owns deterministic generated ground truth and
  kernel-gated frontend generation.
- **[[omega-performance-telemetry]]** owns comparative growth rails.
- **[[grind-port]]** owns whole-solver orchestration and the e-graph interface;
  this issue owns the arithmetic theory module it may eventually call.
- **[[omega-dark-grey-shadows]]** remains an optional measured fast-path
  extension, not a completeness dependency.

## Follow-up owners

- **[[arithmetic-certificate-dag-sharing]]** owns economical proof
  materialization and the end-to-end Pugh rail.
- **[[cutsat-reconstruction-completeness]]** owns the derivation shapes beyond
  the first simple-Cooper slice.
- **[[cutsat-first-class-relations]]** owns direct disequality/divisibility
  reflection.
- **[[shared-arithmetic-reflection]]** owns extracting the representation for
  future arithmetic solvers.

## Log

- 2026-08-27: Landed the substrate's representation boundary in
  `crates/elab/src/arithmetic.rs`: checked affine arithmetic, deterministic atom
  IDs/interning, reflected Nat/Int domains, binary relations, and a generic
  reflected-constraint/evidence record. Omega now consumes those types and
  re-exports its old public names; its division expansion, interval lowering,
  derivations, and proof strings remain solver-local. Focused acceptance pins
  the same nonlinear atom sharing and exact label order through the kernel-
  gated frontend. Do not extract a generic search interface until the first
  CutSat core supplies the second concrete consumer.
- 2026-08-27: Landed the first search-only CutSat consumer in
  `crates/elab/src/cutsat.rs`. It accepts shared affine `Eq`/`Le`, normalizes
  inequalities, constructs ordered integer assignments, learns real
  projections, performs Cooper-Left/Right splits, maintains internal
  divisibility constraints, and combines concrete congruences with generalized
  CRT. Outcomes distinguish checked models, contradiction roots/reachable
  typed derivations, and resource-limited partial state. The boxed 20,000-case
  rail now pins 11,074 models and all 8,926 contradictions (the former 8,835
  real-shadow closures plus all 91 integrality gaps); seed 680 and Pugh's
  nightmare are direct tests. Symbolic interaction among multiple congruences
  above the current two-variable exclusion split, certificate reconstruction,
  and tactic orchestration remain open.
- 2026-08-27: Landed the first kernel-certified fallback route. Omega now sends
  real-shadow survivors through CutSat, whose reachable DAG records normalized
  inequality/divisibility conclusions and explicit Cooper case-premise nodes.
  Heather lemmas certify simple Cooper-Left/Right splits; generated finite
  matches carry refinement equations, open divisibility witnesses, and return
  each resulting linear branch to the ordinary Omega certificate rail without
  recursively re-entering CutSat. The minimized seed-680 gap reaches the kernel
  and reports CutSat search statistics. Pugh remains pinned at the search/DAG
  layer: its naively expanded nested 9-by-9 certificate exceeds the test
  runner's resource ceiling, so cached/named sharing of learned inequalities
  and branch closures is the next reconstruction slice rather than accepting
  exponential source duplication.
