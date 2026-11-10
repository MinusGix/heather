---
title: The unifier's δ-lazy step zonks an n-node arity case tree per arm, quadratic over a wide lemma
status: closed
labels: [elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-11-09
updated: 2026-11-10
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

## Log

- 2026-11-10: Attribution corrected, then fixed. Stack samples of `open_lc` at 360 formers put `unify_ns` in `unification::zonked_tm` under `unify_unfolded`, not in the head walk: the δ-lazy step's guard ("does the pattern still have an open slot?") applies the meta block twice as a global substitution and compares, and the pattern there was `Tm`'s *arity*, a `case` tree whose every node spells the remaining shape (`Fin(n[?a])`-shaped, against the same tree at a concrete label). That walk is superlinear in n, about once per recursive arm. The body above guessed the case descent; it was not that.

  No rule of `unify_tm` reads a pattern headed by an eliminator other than `elimNat`, the projections or a β-redex's λ: such a pairing falls through to `unify_unfolded` at every unfolding of the subject and learns nothing. `inert_pattern` now returns before the zonk for those heads.

  `open_lc`, release, width one: `unify_ns` 93 / 453 / 1,865 ms → 2 / 5 / 18 ms at 90 / 180 / 360 formers; item total at 360 4.5 s → 2.8 s. Every exact counter (steps, queries, misses, unify calls) is unchanged: the step only removed wasted work. `inductive/wide-lemma` slope ~1.1 over three runs (was ~1.2).
