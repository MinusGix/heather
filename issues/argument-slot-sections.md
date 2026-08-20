---
title: Anonymous argument-slot sections
status: open
labels: [frontend,syntax,elaboration,ergonomics]
created: 2026-08-19
updated: 2026-08-19
---

Some checking-position functions immediately feed their incoming arguments
into a larger expression. Naming them adds noise without adding explanatory
scope:

```heather
λ bad => false_elim(bad)
λ x y => f(x, y)
```

Reserve `·` (U+00B7 MIDDLE DOT) as an argument slot, with optional Unicode
subscript digits:

```heather
false_elim(·)       // λ x => false_elim(x)
f(·, ·)             // λ x y => f(x, y)
·                   // λ x => x
f(·₀, ·₀)           // λ x => f(x, x)
f(·₀, ·₂)           // λ x _ z => f(x, z)
```

This is checking-only placeholder abstraction. The smallest enclosing
checking position containing the slots is checked against a Pi telescope,
the required binders are introduced, and each slot is replaced by its local.
It is not a hole, metavariable, implicit argument, or tactic.

## Slot identity and indexing

- A run containing only unindexed `·` assigns distinct positions from left to
  right: 0, 1, 2, ... . This makes the common `f(·, ·)` spelling natural.
- A run containing indexed slots uses zero-based Unicode subscripts. Repeating
  an index repeats an argument; the largest index determines how many binders
  are introduced, so omitted indices deliberately discard those arguments.
- Indexed and unindexed slots may not mix in one abstraction boundary in the
  first design. Refusing `f(·, ·₂)` is clearer than silently choosing whether
  the plain slot means 0, 1, or 3.
- Only subscript digits `₀` through `₉` participate. Multi-digit subscripts
  are read normally (`·₁₂` is position 12); ordinary following numerals are
  separate tokens.

Zero-based indexing follows Heather's general operational convention and
makes the unindexed left-to-right expansion coincide with positions 0, 1, ... .

## Boundaries

- Slot indices refer to consecutive explicit Pi binders at the checking
  boundary. Implicit binders and interaction with named/implicit argument
  insertion need a separate decision before implementation.
- Reordering, repetition, and omission are explicit in indexed mode. Named
  dependencies or explanatory hypotheses use [[sequent-binder-expression]].
- Nested checking positions choose the smallest boundary that can own their
  slots; diagnostics must print that boundary and its expected type.
- A slot outside a checking position is refused rather than defaulted.

## Acceptance

- The five examples above lower to the corresponding ordinary lambdas.
- Dependent Pi telescopes work when later binder types mention earlier slots.
- Repeated and skipped indexed slots have pinned de Bruijn ordering.
- Mixed-mode, out-of-range, inference-position, and non-Pi uses have targeted
  diagnostics.
- Slot discovery does not cross an explicit lambda or sequent-binder boundary.

## What it assumes from elsewhere

- **[[sequent-binder-expression]]** owns the named form. This issue assumes
  only its shared checking-position Pi-introduction semantics.

## Log

- 2026-08-19: Filed from the sequent-binder design discussion. A bare `λ` was
  rejected as the slot token despite making the abstraction mechanism obvious:
  repeated occurrences look like incomplete ordinary lambdas and do not say
  whether they name one argument or several. `·` reads as a mathematical
  argument place; explicit zero-based Unicode subscripts recover identity,
  repetition, reordering, and omission without names.
