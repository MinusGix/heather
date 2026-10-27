---
title: Cut write-elf's linear build constants
status: open
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
