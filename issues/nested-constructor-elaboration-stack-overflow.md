---
title: Elaborating a ~900-deep nested constructor value overflows the native stack
status: closed
labels: [elaborator,robustness]
created: 2026-09-26
updated: 2026-09-28
---

Checking a nested constructor value about 900 levels deep aborts the process
with `fatal runtime error: stack overflow`. A `fn l() → List<Nat>` whose body
is 1,000 nested `list::Cons(…)` reproduces it (800 checks, 1,000 aborts); the
element type does not matter (`List<Int>` aborts at the same depth).

The recursion is the elaborator's, not the kernel's: `gdb` shows about three
frames per element, `build_ctor` → `elab_check_skel_slots` →
`build_children`, from `check_statements` down, on the 8 MiB main stack.
Found while scaling an omega-row probe ([[wf-ih-rebuilt-per-node]]).

A process abort is the wrong refusal ([[kernel-native-depth-budget]]'s rule
for the kernel: `OutOfFuel` with a reason, never an abort). Either the
constructor walk becomes iterative over its right spine, or it runs under a
depth budget and refuses with a diagnostic. Worth checking whether `[…]`
literals take the same path.

## Log

- 2026-09-28: Fixed with a native expression-elaboration depth budget of 512 active
  checking/inference frames (`ExprDepthGuard` in `crates/elab/src/expr.rs`,
  entered by `elab_check_skel_slots` and `elab_infer_at`). This chooses the
  bounded-refusal route: a deep value is refused with an elaboration diagnostic
  at its source span before the native stack is exhausted. Checking and
  inference share the counter, speculative clones inherit its current value,
  and the guard restores it on every return. Guarding only `build_ctor` would
  miss type-parameter inference, which descends into a field before building
  the outer constructor.

  The original 1,000-deep standard-list repro now exits 1 with the diagnostic
  instead of aborting. CLI subprocess regressions run without `RUST_MIN_STACK`
  and cover checked recursive constructors, an inferred let initializer,
  recursive type-argument inference through `Wrap`, and a 100-deep positive
  control that still kernel-checks. An elaborator regression checks that a
  shallow declaration succeeds after the deep one fails.

  Bracket literals do not take the recursive surface-constructor path: they
  lower through the collection-literal protocol's primitive vector. A new
  standard-list acceptance test kernel-checks a 1,000-element bracket literal.
  The budget counts active elaboration calls, not list length or total work.
  An initial 128-frame limit refused existing generated x86 certificates;
  512 preserves those while retaining headroom below the original constructor
  stack-overflow depth on the usual 8 MiB stack.
- 2026-09-28: Validation: the focused constructor/literal tests and generated crossing
  certificates pass. Plain full `scripts/test` reports INCOMPLETE (3,049 passed
  before death, 0 failed): the existing `read_loop_process` group reaches its
  300 CPU-second rail and is SIGKILLed. [[read-loop-process-test-cpu-rail]] owns
  that pre-existing harness failure; the constructor regressions, standard-list
  literal acceptance, generated certificates, and native read/print gates all
  pass. No caps or skip lists changed.
