---
title: wc as a command: GNU behaviours deferred from the first round
status: closed
labels: [native,x86,design]
area: heather-in-heather
created: 2026-10-03
updated: 2026-10-21
---

The full `wc` command (`docs/archive/native-wc-command-design.md`) matches GNU `wc`
9.4 under `LC_ALL=C` except where §2 of that design chooses otherwise. Each
deviation is a fact about the program its claim states, not a gap in the
claim. These are the ones deferred:

- **Diagnostics on stderr.** GNU prints `wc: NAME: <strerror>` for a failed
  open, read or close and a usage message for a bad option. The command
  writes nothing to fd 2 and exits 1 (as `wc -l` does since 2026-09-27).
  This needs an errno-to-message table and `quotef`.
- **Long options** (`--lines`, `--words`, `--chars`, `--bytes`, `--total=`,
  `--files0-from=`, `--help`, `--version`). They are refused as invalid
  options today.
- **`-L`** (maximum line length). It is a max fold over the input. The step
  can carry it, since it grows by at most one per byte, but it is a fifth
  column with its own meaning lemma.
- **Names containing a newline** are printed raw. GNU shell-quotes them.
- **A failed write** exits 1 at once. GNU's buffered stdout finds the
  failure later and also exits 1. The difference is only which syscalls run
  after the failure.
- **stdout stated over what the columns mean.** `{p}_stdout` says stdout is
  `command_stdout` of the state's counts, and `{p}_column{j}_means` says
  slot `j`'s count is `column_means(columns, j)(input)`. A corollary joining
  them, stdout as rows of the columns' meanings over each operand's bytes,
  is stated nowhere yet. Each half is checked; the join is bookkeeping over
  `command_stdout`'s fold.

## What it assumes from elsewhere
- **[[native-wc-as-a-command]]** owns the command and its claim. Assumed
  here: only that stdout and the exit status are stated as functions of the
  command line and the history.

## Log

- 2026-10-07: The stdout-over-column-meanings corollary is the acceptance test of [[command-trace-by-append]].
- 2026-10-21: Closed as not planned: the layer it is about was burned in B1 with the hand-proved native process stack (docs/native/native-program-logic-design.md §3.1, [[native-burn-process-stack]]); the last commit with it is 189659d (tag native-v0). The rebuild states programs as interaction trees and compiles them, so this per-program work does not come back in this form.
