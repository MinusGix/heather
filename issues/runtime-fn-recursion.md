---
title: Compile a runtime fn that recurses, as a procedure within the program's levels
status: open
labels: [native,runtime,recursion,design]
area: heather-in-heather
milestone: [nh-procedures]
created: 2026-11-11
updated: 2026-11-21
---

A `runtime fn` that calls itself other than last is refused: `rt` turns
a measured self-call in tail position into one loop, and a compiled
function calls only functions before it, so nothing it lowers to can
recurse. A recursive-descent parser is the first thing Heather-in-Heather
needs that this blocks. The milestone `nh-procedures` asks that "a
non-tail recursive function compiles"; that holds from the builder
(`Perform`) and not from a `runtime fn`.

`docs/native/runtime-fn-recursion-design.md` is the note this issue asked
for. Since #806 to #812 the stack is asked for in levels of checked calls
(`Source.levels`) and a call past them is a refusal of the compiled
program, not part of the source's meaning; the note replaces the depth
this issue first proposed.

## Scope (the note's §8)

- Built (#824, #832, #836): pure recursion as procedures, the generator
  publishing `f::ptm`, `f::guarded`, `f::unfolds`, `f::fits`, and a closed
  `main` with its levels stated.
- Revised 2026-11-21 (note §3 to §5): the depth is a proved bound,
  `f::fits(d(x), x)`, inferred from the `decreases` measure through a
  per-call decrease companion `f::descends`, tightened by a `depth` clause
  or a theorem; a closed program infers its levels; the stack is a byte
  budget (`runtime(stack := 1 MiB)`) checked once at the recursion's
  boundary; the accumulator rewrite and an opt-in heap stack take a
  recursion off the stack.
- Then calls between `Io` functions ([[rt-effectful-callees]]) with a
  buffer contract, and recursion over `Io` through them.

## What it assumes from elsewhere

- **[[native-one-compiler]]** owns U5. Assumed here: only that a
  procedure has a frame of its own and one contract
  (`Target::Callable`), so a recursion costs a frame a level.
- **[[rt-effectful-callees]]** owns linking procedures from `runtime fn`s
  and the file of words each needs. Assumed here: only that
  `f::program` can hold a procedure.

## Done when

A non-tail recursive `runtime fn` (`port_depth`, then a small
recursive-descent recogniser) compiles, runs natively against its
Heather meaning on inputs whose `f::depth` is within the program's
levels, and stops with the call-depth status one past them, with nothing
proved for the function in particular.
