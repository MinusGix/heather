---
title: Elaborate unindexed recursive constructor values with an explicit work stack
status: closed
labels: [elaborator,robustness]
created: 2026-09-28
updated: 2026-09-28
---

[[nested-constructor-elaboration-stack-overflow]] now refuses deeply nested
expressions safely, but the native expression budget still limits ordinary
constructor values. Make checking of saturated, unindexed recursive
constructors use an explicit work stack, starting with plain recursive fields
(lists and trees). Keep the existing budget for other elaboration routes.

Preserve expected-type constructor resolution, local shadowing, payload
checking, traversal order, emitted annotations, diagnostics, and the real
kernel gate. Unsupported constructor forms must fall back to ordinary
elaboration. Avoid a separate List-specific encoding.

Acceptance: the original 1,000-deep standard-list constructor expression
kernel-checks successfully; also cover branching trees, open element types,
checking positions, and wrong field/type and shadowing controls. Bracket
literals remain supported. Parser and kernel depth limits remain separately
owned.

[[constructor-argument-subtree-copying]] owns copies made while routing and
partitioning constructor arguments; this issue owns replacing recursive
constructor descent with an explicit work stack.

## Log

- 2026-09-28: Implemented an explicit constructor work stack for saturated, unindexed
  constructors in plain recursive fields. Each frame prepares the existing
  label and shared emission slots, checks the container tail first, visits
  plain children in the previous reverse order, and attaches their checked
  terms using the same literal-arity pair encoding. Payload checking remains
  with the existing field/skeleton builder; name resolution and named argument
  permutation retain their existing owners. The family, expected type and
  context are constant across plain recursive children.

  Other expressions, written type applications, indexed recursion, and free
  argument-slot sections retain ordinary guarded checking. This scope is an
  intentional first implementation, not a promise that every surface-expression
  form is now iterative. The guard remains useful for deeply nested type-argument
  inference before constructor building begins.

  The original 1,000-deep standard-list case now kernel-checks, with one manual
  list warning. CLI tests accept deep checked and inferred list spines without
  RUST_MIN_STACK. Additional controls cover deep left- and right-branching trees
  with open element types and ambiguous constructor names, child order, wrong
  payload and nominal types, and locally shadowed constructor names. Manual
  list lint recognition is iterative and stops rescanning spans already warned
  about. [[constructor-argument-subtree-copying]] owns the borrowing change
  under this walk.
- 2026-09-28: Final verification: plain full `scripts/test` reports INCOMPLETE (3,053 passed
  before death, 0 failed). The existing read-loop mutation group is killed at
  its CPU rail; [[read-loop-process-test-cpu-rail]] owns this unchanged harness
  failure. Constructor, standard-list, indexed/fording, named/record/container,
  unit, native certificate, and documentation checks pass. Caps and skip lists
  are unchanged. The original standard-list CLI reproducer also checks with
  the release compiler.
