---
title: Elaborating a ~900-deep nested constructor value overflows the native stack
status: open
labels: [elaborator,robustness]
created: 2026-09-26
updated: 2026-09-26
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
