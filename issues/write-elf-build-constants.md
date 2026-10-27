---
title: Cut write-elf's linear build constants
status: closed
labels: [native,cli,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-27
updated: 2026-10-27
---

`write-elf`'s build is linear in the code since
[[native-compile-linear-layout]], and builds programs at the file limit
under the suite's rail ([[native-compile-capacity]]'s log has the sizes).
What is left are constants, in the order the timings rank them:

- **The code literal is elaborated twice**: the fork's read module and the
  certificate each elaborate `{p}_at_k`, and an `At`/`Start` constructor
  costs about a hundred `instance_match` calls in gendefs (per-instantiation
  type codes, `crates/elab/src/gendefs.rs`). Together the largest family.
  The read module needs the literal only for the byte pieces' reads, which
  could read by the emission's parts instead; the per-constructor cost is
  an elaborator question worth its own look if it shows up elsewhere.
- **The shape read holds every leaf's emission**: `Source::shape` evaluates
  `Stmt::leaf_shape` (each leaf's emission, for its label names) in one
  evaluation, so its arena grows with the program; it is the largest
  memory row, linear. Reading the shape a subtree at a time, or a leaf's
  names without its code, bounds it.
- **The `upto` chain** (`{p}_upto_c_is`) converts `asm_back({p}_code(), back)`
  per piece, so it grows slightly faster than linear; stating it over the
  literal's cut definitions, as the pieces now are, removes that.

## Done when

The literal is elaborated once, and the shape read's peak no longer grows
with the program.

## Log

- 2026-10-27: done, all three.
  - **Literal once.** The fork no longer elaborates the literal: once the
    parts are read and the label table is known, the same fork reads the
    bytes a read at a time over each read's own program at `Start` (a part's
    emission again, or the items around parts), by `asm_code_ending` with
    the read's end offset and the table's labels
    (`emission::byte_reads`). The cost is each part emitted a second time,
    a small fraction of what the literal cost. The literal's own constant,
    about ten `instance_match` calls per `At`, is now
    [[constructor-literal-respell-cost]].
  - **Shape.** `Source::shape` counts a leaf's label names
    (`Stmt::leaf_names`) instead of emitting it, so the read holds the
    tree's numbers only; it takes no layout any more. Probes in
    native_compile_tests pin the count to the emission for every leaf kind
    that takes names, and `emission.rs` refuses a shape whose counts a
    `Then`'s or `Branch`'s join would not accept, before the kernel does.
  - **`upto`.** Each piece and each `upto` step is stated over the
    literal's definition where its window ends (`{p}_at_{top}`), not
    `asm_back({p}_code(), back)`, so a step walks back over its own piece.

  Width one, cloud box, fresh copy of a warmed cache
  (perf/fixtures/native_sizes/run.sh), master b08e09d against this:

  | probe  | before | now   |
  |--------|-------:|------:|
  | cat_x4 | 76 s   | 56 s  |
  | cat_x8 | 138 s  | 104 s |

  At cat_x8 the read module's `at_k` (31 s) and piece reads (13 s) are
  replaced by the byte reads (15 s); the shape read's peak-growth row
  (343 MB) is gone from the memory table, whose largest row is now the
  library. Left, in order: the certificate's literal (30 s,
  [[constructor-literal-respell-cost]]), the pass (19 s), the byte reads
  and the pieces' kernel evaluation (15 s and 12 s, both mostly encoding
  the instructions).
