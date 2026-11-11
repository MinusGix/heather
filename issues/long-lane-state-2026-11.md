---
title: The long self-check lane had stopped building; what it says now that it runs
status: open
labels: [kernel,testing,elaboration]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

`scripts/test --long` builds the kernel with `long-checks`, which runs every
slow self-check every time instead of one in sixteen
(`crates/kernel/src/checks.rs`). It is the sweep a round touching the
kernel's traversals or its bounds owes. It had not run since the kernel
library became a package of its own: the script asked Cargo for
`heather-kernel/long-checks`, a feature that moved to `heather-kernel-lib`,
and stopped at the error. Nothing noticed, because nothing runs the lane on a
schedule.

It runs again (2026-11-10, the one-line fix to `scripts/test`). Its first
whole run, on the branch that put the free-variable bounds in the node
([[free-variable-bounds-in-the-node]]), did not pass. What it said, by cause:

## Fixed with it

- **The self-checks nested** ([[self-checks-nest]], closed). The kernel's
  unit tests, `kernel/tests/deep_terms.rs`, `elab/tests/let_and_blocks.rs`
  and `elab/tests/iwf_no_confusion.rs` ran into the stack or the CPU rail.
  On master's own long build `let_and_blocks` fails the same way and
  `deep_terms` passes: that one came with the branch. The other two were
  not run on master; the typing memo's nesting does not depend on the
  branch.

## Open

- **A readback disagrees with the reducer**, on master too:
  `indexed_families::append_and_definitional_index_arithmetic` panics in
  `crates/elab/src/readback.rs` (`verify`: "readback respelled a weak head
  reduct"). Reproduce with
  `scripts/test --long -p heather-elab --test family_indexed`. The probe is
  the weak head form of `V<Nat>(add(1, 2))` from `build_indexed_ctor`, a
  family defined by recursion on its index. Both sides agree up to the
  index of the recursive occurrence, the predecessor of `add(1, 2)`:

  ```
  reducer:  … elimN[1](M Ty 0; z …; s …; elimN[0](M Nat; z 1; s S(x0); 1))
  readback: … elimN[1](M Ty 0; z …; s …; 2)
  ```

  The reducer's scrutinee is weak head normal at `S(add(1, 1))` and its
  predecessor is that unevaluated call. The machine's is a number, so its
  predecessor is the number `2`, and `Readback::val` spells a number's
  predecessor as a literal on the assumption that the reducer's scrutinee
  was a literal too (`Val::NatRun` over `Zero`). The check's own comment
  says a disagreement is not unsound, since the kernel re-checks every
  term, and that the elaborator anchors on spellings in places. One probe
  in sixteen is compared by default, which is how this one stayed out of
  sight.
- **Five library modules run into the 300 s CPU rail** in
  `cli/tests/library.rs` with every check on: `native_build_parts`,
  `sha256_round`, `native_compile_correct`, `sha512_round`,
  `runtime_sint_loops_tests`. Measured before [[self-checks-nest]] was
  fixed, so some or all of it may be the nesting; to be read again from a
  run over the fix (this issue's log).
- `cli/tests/native_cat.rs` and `native_tools.rs` had not finished after
  seventeen minutes each when that first run was stopped.

## What would keep it from rotting again

The lane is described as a sweep, not a gate, and that is right for its
cost. But a lane nobody runs is a lane whose feature name can be wrong for
weeks. Cheap options: have the nightly sentinel build (not run) the long
target, so the feature and the build stay true; or have it run the kernel's
own tests under the lane, which is seconds once the checks do not nest.

## Log

- 2026-11-10: The whole lane over the self-check fix ([[self-checks-nest]]), cloud box, `scripts/test --long` on a cold `target/long`: **3909 passed, 2 failed, 2 ignored**, compile 234 s and tests 1928 s. Before the fix the lane did not finish: the kernel's own unit tests, five library modules and the native tool gates sat at their rails. What is left:

  - `indexed_families::append_and_definitional_index_arithmetic`, the readback disagreement above. Unchanged, still open.
  - `native_linked::linked_exports_are_what_the_compiler_emits`: a rail, not a disagreement. Three `compile-x86 lib/lang/lexer/lexer_scan.hthr` children ran at once and each needs about the whole 300 s CPU rail with every check on (`scan_begin` finished at 96% of it, `scan_step` and `scan_accept` were killed at 98%). The default lane's same children are far inside it. Either the long lane gives this gate the write-elf gates' longer rail, or it is the lane's standing measure of what the scanner's certificate costs under full checking.

  Everything else passes with every check on every occasion, the whole-library gate included (`crates/cli/tests/library.rs`, 1808 s of wall and two `heather check` children at 95% and 98% of the rail, so it is one slow box away from the same kind of red) and `native_cat`, `native_tools`, `native_program`, `native_branches`.
