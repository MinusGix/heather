---
title: Pin Omega search and certificate growth telemetry
status: open
labels: [proofs,performance,arithmetic,testing]
area: tactics
created: 2026-08-27
updated: 2026-10-28
---

Turn Omega's existing audit data into explicit scaling rails. Measure total and
reachable derivations, discarded work, peak constraint-frontier size,
generated certificate source size, and reconstruction/checking time on stable
adversarial families.

The same report must separate ordinary Omega, CutSat search, and CutSat proof
reconstruction so fallback improvements remain attributable. In particular,
[[arithmetic-certificate-dag-sharing]] owns reducing large proof DAGs while this
issue owns the source-size/check-cost rails that demonstrate the reduction.

The purpose is regression detection rather than a universal benchmark. Counts
that are deterministic should be pinned exactly; wall-clock measurements
should be recorded or bounded coarsely enough to remain reliable. Include
equality chains, dense Fourier--Motzkin projections, balanced hard equalities,
division auxiliaries, and repeated shared opaque atoms.

## Acceptance

- `OmegaReport` exposes every deterministic count needed by the scaling rails,
  including peak frontier size.
- Dedicated tests demonstrate certificate sharing and detect accidental
  exponential reconstruction growth.
- Slow families live in an independently schedulable target with recorded
  timing history.
- Telemetry never changes the trusted certificate boundary.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns audit reports and derivation sharing.
- **[[test-suite-target-timing-and-slow-lane]]** owns runner scheduling.

## Log

- 2026-09-04: Sibling filed 2026-09-04: [[omega-per-goal-elaboration-cost]] owns attributing and reducing the tens of seconds one ordinary linear goal (cutsat_left_cut, 55 s) takes to elaborate; this issue stays the rails that detect regression.
- 2026-09-05: OmegaReport grew a 'phases' field (OmegaPhases, per-invocation wall time by phase) in the [[omega-per-goal-elaboration-cost]] round, 2026-09-05; the counts this issue owns are untouched.
- 2026-09-22: 2026-09-22: After the app@ round the CutSat lemmas lead the perf corpus; attribution question filed as [[omega-cutsat-lemma-cost]]. A clean probe of per-certificate check cost: an identity goal h : a < b ⊢ a < b over two list_len atoms checks in 224 ms ([[measure-obligation-omega-on-a-written-proof]]).
- 2026-09-23: Correction to the 2026-09-22 entry: the calc_parser goal was not an identity. It was a mutual group's scaled obligation, and those sites now close without omega ([[measure-obligation-omega-on-a-written-proof]]). The per-certificate cost it pointed at stands: a two-variable linear Nat goal costs 200-500 ms per item cold (elaborating a ~5 KB certificate, then gating it), whatever the atoms.
- 2026-10-28: Tracker tidy: dropped `blocked-by: [omega-linear-arithmetic]`. That issue is closed (the affine solver and its certificates landed), so nothing blocks this one; its scope here is unchanged.
