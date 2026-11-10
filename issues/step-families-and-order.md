---
title: Step families: a program in a step, its limit and its order of convergence
status: open
labels: [stdlib,mathematics,analysis,reals,continuous-time]
area: mathematics
milestone: [math-reals]
created: 2026-11-10
updated: 2026-11-10
---

A vocabulary for a program written against a step, and what its limit says
about any one run (`docs/continuous-time-survey.md` §3 reading (A), §5.2
item 1). Probes of the shape, at `Rat`:
`lib/_tests/std/analysis/continuous_time_tests.hthr` (`dt_linear_error`,
`dt_transfer_le`, `fall_richardson`).

Scope, generic over an ordered field:

- a family indexed by resolution with a limit and an *order*: a record
  holding `l`, `C`, `p` and the bound `|xs(k) - l| <= C·dt(k)ᵖ`, from which
  `Converges` follows with a modulus that is read, not searched;
- transfer lemmas as corollaries of the limit rules: closed relations
  (`<=`, `≈`) and images under uniformly continuous maps pass from every
  step to the limit;
- Richardson's combination as a theorem: a family with error
  `c·dt + O(dt²)` gives one of order 2 from two runs, and the general step
  from order `p` to `p + 1`.

The second bullet is the constructive form of Imada and Hsu's Transfer rule
(arXiv 2611.12761); the first is what their semantics lacks, and it is the
link between a run at a real step and the continuous answer.

## What it assumes from elsewhere

- **[[real-completeness-interfaces]]** owns `Converges`, `CauchySeq` and
  `CauchyComplete`. Assumed here: only the limit rules in `sequence.hthr`.
- **[[certified-expansions]]** owns expansions with a certified remainder.
  Assumed here: nothing yet; an error expansion in the step is an instance
  of its record once that exists, and the Richardson theorem should be
  restated over it then.

## Log
