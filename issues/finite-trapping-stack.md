---
title: Develop a finite trapping stack and representation interface
status: open
labels: [stdlib,semantics,design]
created: 2026-08-25
updated: 2026-08-25
---

A small abstract stack lets proofs about evaluation, calls, resource bounds,
and protocols live in a list-and-arithmetic world.  It should support a finite
capacity and explicit underflow/overflow outcomes so that later refinements to
machine memory do not smuggle in an infinite stack.  It is not itself the x86
stack: real x86 stack instructions update ordinary memory and RSP.

Build the datatype and law kit independently, then define the interface a
concrete state representation must satisfy to claim that it represents an
abstract stack.  That representation interface is the bridge by which a
machine-specific `PUSH` theorem can reuse generic LIFO and capacity results.

## Acceptance

- Define a generic finite stack with capacity, contents, and an explicit
  operation outcome distinguishing success, underflow, and overflow.
- Provide empty, size/capacity, peek, push, pop, and a sequential operation
  runner or fold useful for reasoning about call sequences.
- Prove LIFO (`push` then successful `pop`), size/capacity changes, preservation
  on rejected operations, and laws for sequences that remain within capacity.
- Relate the finite stack to the existing `List` API rather than duplicating
  list traversal and length arithmetic.
- Define a representation relation/interface abstract enough for a concrete
  state with a pointer plus addressed storage.  Prove a toy implementation
  refines push and pop under explicit valid-range/access premises.
- Keep growth/allocation policy separate: a growable stack is a client built
  from allocation outcomes, not an ambiguity in finite `push`.
- Record proof/API friction exposed by neutral capacity and element type, not
  only closed examples.

## What it assumes from elsewhere

- **[[byte-memory-access-model]]** owns the eventual byte-memory customer of
  the representation interface; the abstract stack can land using `List`
  before byte memory exists.
- **[[relational-semantics-refinement-kit]]** owns generic refinement and
  sequential relation composition.
- **[[memory-bound-certificates]]** owns allocation/capacity assumptions at a
  platform boundary.  This issue owns the finite container laws given a
  capacity.

## Log

- 2026-08-25: Filed as a deliberately simple proof world that must refine to,
  rather than replace, any later concrete machine stack semantics.
