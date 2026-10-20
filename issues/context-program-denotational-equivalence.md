---
title: Decide denotational equivalence of differently shaped context programs
status: open
labels: [kernel,conversion,performance,representation,research]
area: kernel
created: 2026-09-01
updated: 2026-09-01
---

`ContextProgram<C>` is a straight-line program for a sequence of one-hole
constructor contexts. Pointer identity, equal runs, and bounded pairwise DAG
bisimulation now cover the representations the kernel ordinarily produces,
including independently allocated depth-64 doubling DAGs. Prefix cancellation
also crosses ordinary composition and run boundaries when it can expose or
skip a shared/bisimilar front.

That sufficient relation is not complete for compressed strings. Two programs
can denote the same context sequence while having unrelated association,
sharing, and run segmentation. Flattening both cursors may take time
proportional to the exponentially large denotation even though each input DAG
is small. A complete solution is an SLP equality/longest-common-prefix
algorithm, not deeper recursive term comparison.

This is not an active blocker: literal runs, saturated compositions, shared
programs, and independently rebuilt versions of the same construction all
stay compact. Keep the stronger problem explicit rather than silently turning
the bounded bisimulation into a claimed decision procedure.

## Acceptance

- Decide equality and find unequal residuals for semantically equal-prefix
  programs with adversarially different association and run boundaries in
  polynomial work in compressed input size.
- Keep all work iterative and bounded by the caller's existing kernel fuel;
  exhaustion is not a positive or negative verdict.
- Preserve context genericity: no Nat, relation, inductive-constructor, or
  global-name cases.
- Test equal, unequal, and prefix-related SLPs whose denotations are too large
  to enumerate, including independently allocated inputs with no shared
  pointers or matching tree topology.

## Likely direction

Use a standard compressed-word equality/LCP technique over the acyclic
straight-line grammar, with run nodes treated as weighted terminals. Any
memoization key must be scoped to one comparison and retain every keyed node,
as the bounded bisimulation does now, so raw pointer identities cannot be
reused while they remain keys. The algorithm must expose compact residual
programs rather than merely decide equality, because
synchronous folds and conversion both need to resume at the unmatched tails.

## What it assumes from elsewhere

- **[[succinct-inductive-values]]** owns the representation, ordinary
  producers, and structurally recognized consumers. This issue owns only
  completeness across different compressed spellings of the same context
  sequence.
