---
title: timings test reads the table before SIGSTOP has stopped the process
status: open
labels: [tooling,infrastructure,testing]
area: infrastructure
created: 2026-11-25
updated: 2026-11-25
---

`crates/cli/tests/timings.rs`'s `a_killed_run_leaves_its_rows_and_what_was_running`
failed once under `scripts/test --pr` on 2026-11-25, while the whole-library
gate was loading the machine, and passed 3/3 run alone straight after on the
same tree (`claude/loops-round-d2`, a branch that changes nothing under
`crates/cli/src`):

```
assertion `left == right` failed
  left: "scope\tmodule\titem\nrun\t\t\n"
 right: "scope\tmodule\titem\nrun\t\t\nitem\tprelude\tsym\n"
```

The table read after the kill had *one row fewer* than the table the test
had seen while the process was stopped.

The test stops the child with `kill -STOP`, then reads `t.tsv` and
`t.open.tsv` straight away (timings.rs, the loop before the kill). `kill`
returns once the signal is sent, not once every thread of the target has
stopped: a multi-threaded `heather check` can still be running, and writing,
for a moment after. So "what was seen" and "what the kill finds" can differ.
That a row *disappeared* also suggests the table is rewritten in place, not
only appended, so a reader can meet it mid-rewrite. That would matter beyond
the test: the table is meant to survive a run killed at the rail (CLAUDE.md).

## Done when

The test waits until the child is actually stopped (`/proc/<pid>/stat`
state `T`) before reading. If the writer rewrites the table, it does so
atomically (write a temporary file and rename it), or appends only. The test
passes repeatedly under a loaded machine (e.g. alongside the library gate).
