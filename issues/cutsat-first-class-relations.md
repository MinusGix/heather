---
title: Reflect disequality and divisibility directly into CutSat
status: open
labels: [proofs,elaboration,arithmetic,solver]
area: tactics
milestone: [tac-arith]
created: 2026-08-27
updated: 2026-11-08
---

Make integer disequality and divisibility first-class reflected inputs instead
of obtaining them mainly through logical splitting or internal Cooper state.
Preserve written source evidence and deterministic atom sharing, then pass the
typed constraints directly to CutSat with structured model validation and
kernel reconstruction.

## Acceptance

- Ordinary source propositions for `≠` and divisibility reflect without an
  eager two-way logical split when CutSat supports them directly.
- Candidate models validate every reflected relation.
- Contradictions reconstruct through explicit witness/exclusion lemmas, with
  satisfiable mutations and unsupported forms returning structured state.

## What it assumes from elsewhere

- **[[cutsat-linear-integer-arithmetic]]** owns CutSat constraint semantics.
- **[[cutsat-reconstruction-completeness]]** owns proof replay for the resulting
  derivations.

## Log

- 2026-10-28: `≠` half landed: Omega's frontend reflects a context `x ≠ y` at Int (and Nat via `Int::ofnat_ne`) as `Relation::Ne` with evidence `omega::normalized_ne_value`, CutSat reads it via `assume_ne`, and the eager two-way split is skipped once CutSat has a model. Eight disequalities on one variable used to be 2⁸ Omega runs. Refusals print CutSat's integer model. Left: written divisibility `d ∣ e` and `¬(d ∣ e)` still go through the remainder (`mod`) reflection and the split; reflecting them as CutSat divisibility (`assume_dvd`) is what remains here.
- 2026-11-08: Related reader gap: [[omega-reads-min-max]] (max/min read as atoms).
