---
title: Compile a runtime fn that recurses, as a procedure with its depth in the meaning
status: open
labels: [native,runtime,recursion,design]
area: heather-in-heather
milestone: [nh-procedures]
created: 2026-11-11
updated: 2026-11-11
---

A `runtime fn` that calls itself other than last is refused: `rt` turns
a measured self-call in tail position into one loop, and a compiled
function calls only functions before it, so nothing it lowers to can
recurse. A recursive-descent parser is the first thing Heather-in-Heather
needs that this blocks. The milestone `nh-procedures` asks that "a
non-tail recursive function compiles"; that holds from the builder
(`Perform`) and not from a `runtime fn`.

`docs/native-procedures-are-functions-design.md` §2.8 gives the shape:
the function reflects to a procedure whose body `Perform`s itself, each
call a statement, and it publishes its tree at a depth: the Heather
function's value where the depth covers the recursion at that argument,
and the exit with `call_depth_status` otherwise.

## Scope

- A lowering of a pure term with self-calls to a `Stmt`, each call a
  `Perform`, proved once against the term's meaning under a depth that
  suffices.
- What states the depth a call needs: a generated companion function by
  the same recursion, or a bound the user proves. This is a surface
  question and wants its own short note before the code.
- The generator's dispatch: a function with a self-call that is not last
  takes this route and publishes the run under the depth premise in
  place of `f::agrees`.
- Mutual recursion between `runtime fn`s through the same route.

## What it assumes from elsewhere

- **[[native-one-compiler]]** owns U5. Assumed here: only that a
  procedure has a frame of its own and one contract
  (`Target::Callable`), so a recursion costs a frame a level.
- **[[rt-effectful-callees]]** owns linking procedures from `runtime fn`s
  and the file of words each needs. Assumed here: only that
  `f::program` can hold a procedure.

## Done when

A non-tail recursive `runtime fn` (a tree walk or a small
recursive-descent recogniser) compiles, runs natively against its
Heather meaning on inputs within the depth, and exits with the depth
status one past it, with nothing proved for the function in particular.
