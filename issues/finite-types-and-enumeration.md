---
title: "Finite types: a class with enumeration, instances, and quantifiers decided by evaluation"
status: open
labels: [stdlib,mathematics,finite]
area: mathematics
milestone: [math-finite]
created: 2026-11-10
updated: 2026-11-10
---

From the foundational-mathematics ranking Minus accepted on 2026-11-10
(`docs/roadmap.md` log, that date), area 1.

The library has no notion of a finite type. `Fin` is a builtin whose one
library use outside `lib/std/num/float` is `List::at`. Every client that
ranges over a finite carrier (register sets, opcode forms, DFA states, the
float formats' digit ranges) brings its own list and its own "this list is
everything" lemma.

## Scope

- A class for a type with a duplicate-free list of all its elements
  (name to be chosen against `lib/std/num/float`'s `Finite(F)`, which is
  taken), with membership of every element as a field.
- Instances: `Fin n`, `Bool`, `Unit`, bytes and words at a literal width,
  products, sums, `Option`, and enums through `derive`.
- `Decide` for `∀ x, P(x)` and `∃ x, P(x)` over an instance with decidable
  `P`, by folding the list, so a closed claim is `b = True` by `refl`
  (`docs/proof-patterns.md`, closed verdicts).
- Probes in `lib/_tests` on all four axes of
  `docs/testing-generated-terms.md` for the derived instance.

## Done when

A client proves an exhaustive claim over an enum and over `Fin n` at a
literal `n` by `decide`, with no enumeration lemma of its own, and
[[finite-cardinality-and-pigeonhole]] can start.

## What it assumes from elsewhere

- **[[finite-set-enumeration-and-folds]]** owns enumeration of finite
  *sets*. Assumed here: only that a finite type's full set is one of them.
- **[[automation-lemma-registries]]** owns how a new instance reaches
  tactics. Assumed here: nothing yet; instances are ordinary class
  instances.
