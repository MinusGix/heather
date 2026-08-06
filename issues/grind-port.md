---
title: A grind of our own, whose failures hand back the e-graph
status: open
labels: [tooling,elaboration,metaprogramming,design]
created: 2026-08-05
updated: 2026-08-06
---

From the 2026-08-05 riff under [[ai-facing-tooling]]: the plan to
port/implement our own version of Lean's grind (congruence closure +
e-matching + case splits), recorded with its design centerpiece. Not
scheduled.

The centerpiece: **the stuck state is the interface, not the
annotations**. When grind fails it holds a rich partial state — the
equivalence classes it built, the instantiations it tried, the patterns
that never fired, the splits it did not take. Every existing prover
throws that away and prints "failed". Ours dumps it as structured data,
because the asymmetry runs our way: a human glazes over at a 200-line
e-graph summary; a model reads it and answers "it never learned
append(xs, Nil) = xs — add that". The loop becomes run -> read stuck
state -> add one hint -> rerun, each iteration mechanical and cheap.
This is NOT AI-in-the-core-loop: the solver stays deterministic and
certifying; the model sits at the hint interface where tedium was the
only barrier. Throwing a dozen annotations at grind is tedious for a
human and casual for a model — provided the used ones are reported back
([[lemma-selection-and-search]] piece 3) so spray does not rot into the
committed file.

Certifying throughout: grind emits a term, the kernel checks it, the
e-graph never enters the trusted story.

## What it assumes from elsewhere
- **[[lemma-selection-and-search]]** owns the hint-pool language and
  used-subset reporting. Assumed here: only that a solver can receive a
  pool and report usage.
- **[[surface-proof-automation]]** owns the solver slot
  (`on _: _ := solver(goal)`). Assumed here: only that grind is one
  more solver behind that slot, not a new surface form.

## Log

- 2026-08-06: Cross-ref (2026-08-06): [[parallel-checking-and-caching]]'s rung-2 trace format was sharpened to a goal-keyed decision tree with a deterministic reconstructor; the e-graph this issue hands back on failure should be (a serialization of) that same object, so grind's design inherits the three format rules recorded there.
