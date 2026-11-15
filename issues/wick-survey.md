---
title: Survey Wick, the Lean ML formalization, for what Heather should take
status: closed
labels: [research,design]
area: machine-learning
milestone: [ml-survey]
created: 2026-10-20
updated: 2026-10-21
---

Owns the roadmap's `ml-survey` milestone (`docs/roadmap.md`). Wick is
Minus's Lean project formalizing a good amount of machine learning, not
touched for a while. Before anything is ported, survey it:

1. What it formalizes, module by module, and which results are worth having
   in Heather.
2. What should be done *fundamentally better* rather than transcribed:
   Minus's own judgement is that it needs real work.
3. The mathematics it needs from Heather (linear algebra, analysis,
   probability, floating point) and the programming tooling (tensors as
   data, numerics), each mapped to a roadmap milestone or a new issue.

The output is a short doc under `docs/` and a list of follow-up issues in
the `machine-learning` area.

## What it assumes from elsewhere

- **[[floating-point-formalization]]** owns floats. Assumed here: only that
  ML accuracy claims will be stated over it.

## Log

- 2026-10-21: Surveyed at Wick `b1b88a2`: `docs/surveys/wick-survey.md`. Follow-ups:
  [[ml-tensor-shapes]], [[ml-layers-reverse-mode]], [[ml-scalar-refinement]],
  [[ml-gaussian-states]], [[ml-deterministic-descent]] (machine-learning);
  [[finite-linear-algebra]], [[real-functions-and-derivatives]],
  [[set-partition-combinatorics]], [[finite-probability]] (mathematics).
  Proposed ML milestones are in the doc's §6, not yet in the roadmap.
