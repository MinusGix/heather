---
title: Gradient descent convergence under smoothness and strong convexity
status: open
labels: [mathematics,machine-learning]
area: machine-learning
created: 2026-10-21
updated: 2026-10-21
---

The first optimisation theorems (`docs/wick-survey.md` §2.2): L-smoothness
and the descent lemma, strong convexity and the PL inequality, and linear
convergence of gradient descent with step `1/L`, over `Fin n → R` at an
ordered field where the proof allows it. Wick has these classically
(`Convergence/Convex.lean`, `PL.lean`) over Mathlib's `fderiv`.

Include one known-answer instance (a quadratic with a concrete matrix at
`Rat`) whose constants and iterates are checked by evaluation, in the manner
of Wick's toys. Statements follow the survey's §3.3 convention: problem data
in a record, the regime as one named predicate, constants as definitions.

## What it assumes from elsewhere

- **[[real-functions-and-derivatives]]** owns derivatives. Assumed here: a
  gradient for functions on `Fin n → R`, or the formal one for quadratics.
- **[[finite-linear-algebra]]** owns quadratic forms and their bounds.

## Log
