---
title: The unifier's head walk descends an n-arm Wf case tree by substitution, quadratic over a wide lemma
status: open
labels: [elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-11-09
updated: 2026-11-09
---

After [[wide-inductive-lemma-quadratic-gate]], the lemma `Tm::open_lc` over an
`n`-former syntax is linear in the gate and in most of elaboration. One
elaborator term stays quadratic: the unifier's `unify_ns` time, which is
small at 90 formers and dominates elaboration from a few hundred on (it
roughly quadruples per doubling of `n`, while the rest of the declaration
doubles).

Attribution: the unifier's small-step head walk (`Unfold::NextHead`, a
bounded number of `reduce` steps) descends the Wf step's right-nested case
tree one constructor at a time. Each `case` step substitutes into the
remaining tree, so reaching arm `i` copies the arms after it, and every arm
of the lemma pays work linear in the number of *other* constructors. The
refold (`crates/elab/src/refold.rs`) only fires at the ι-redex itself; the
case descent before it is the residue.

## Directions

- Let the head walk descend a closed case tree by evaluation (the value
  machine already selects an arm without substituting into the others) and
  read back only the selected arm.
- Or give the Wf step an arm table (a constructor-indexed selection the
  reducer indexes into) so `case` descent is one step, which would also
  shorten the kernel's spelling.

## Acceptance

`scripts/bench-frontend --filter wide-lemma` at sizes past 128 formers
holds an exponent near one, and `unify_ns` in a `--timings` run of the
probe grows linearly.
