---
title: Develop a bounded list, trapping stack API, and representation interface
status: open
labels: [stdlib,semantics,design]
created: 2026-08-25
updated: 2026-08-25
---

A bounded list is the common logical core: a capacity, `List` contents, and
an internal proof that the contents fit.  Its ordinary `push` and `pop` API is
already a stack when clients restrict themselves to those operations.  This
lets proofs about evaluation, calls, resource bounds, and protocols live in a
list-and-arithmetic world while explicit underflow/overflow outcomes prevent
later refinements to machine memory from smuggling in an unbounded stack.
It is not itself the x86 stack: real x86 stack instructions update ordinary
memory and RSP.

The fit proof belongs in the datatype rather than being threaded through every
operation.  It is observationally irrelevant: whether the bound holds matters,
but which proof established it must not affect equality of bounded lists.
Therefore the field uses the user-facing squash owned by [[sprop-squash]].
An ordinary proof-relevant field would make even `pop(push(x, s)) = s` depend
on equality between the reconstructed bound proof and the proof stored in `s`.

Build the datatype and law kit independently, then define the interface a
concrete state representation must satisfy to claim that it represents an
abstract stack.  That representation interface is the bridge by which a
machine-specific `PUSH` theorem can reuse generic LIFO and capacity results.

## Acceptance

- Define a generic `BoundedList<A>` with capacity, `List<A>` contents, and a
  squashed proof that `len(contents) <= capacity`.
- Give `BoundedList` an explicit operation outcome distinguishing success,
  underflow, and overflow.
- Provide empty, size/capacity, peek, push, pop, and a sequential operation
  runner or fold useful for reasoning about call sequences.
- Prove LIFO (`push` then successful `pop`), size/capacity changes, preservation
  on rejected operations, and laws for sequences that remain within capacity.
- Define operations and laws through the existing `List` API rather than
  duplicating list traversal and length arithmetic.  The head is the top for
  the stack reading of the API.
- Define a representation relation/interface abstract enough for a concrete
  state with a pointer plus addressed storage.  Prove a toy implementation
  refines push and pop under explicit valid-range/access premises.
- Keep growth/allocation policy separate: a growable stack is a client built
  from allocation outcomes, not an ambiguity in finite `push`.
- Record proof/API friction exposed by neutral capacity and element type, not
  only closed examples.
- Do not add a distinct unbounded `Stack`: `List` already supplies that proof
  world.  Also do not add a bounded-stack wrapper in this round.  Such a
  wrapper becomes useful only if a later customer needs a type whose clients
  cannot use arbitrary list operations, for example proofs about rewrites of
  stack-only programs.

## What it assumes from elsewhere

- **[[sprop-squash]]** owns user-facing irrelevant evidence and its restricted
  eliminator.  Assumed here: `BoundedList` can store the squashed fit proof,
  derive another squashed side condition without inspecting its witness, and
  compare reconstructed values without comparing fit proofs.
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
- 2026-08-25: Design discussion replaced a dedicated finite-stack datatype
  with `BoundedList`: capacity and contents are general, while plain `push` and
  `pop` supply the stack API.  The validity proof lives in the value and is
  squashed; a separate wrapper is deferred until restricting clients to stack
  operations has a proof customer.  This promotes [[sprop-squash]] from an
  unscheduled foundation item to this issue's direct prerequisite.
- 2026-08-25: UNBLOCKED: [[sprop-squash]] landed. The optional derived
  combinator polish is owned by [[squash-library-api]] and does not prevent
  implementing the container with `squash_ind` directly.
