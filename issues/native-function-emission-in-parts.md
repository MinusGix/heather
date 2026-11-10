---
title: Emit a function a region at a time, so the budget bounds a region and not the function
status: open
labels: [native,compiler,performance]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-10
updated: 2026-11-10
---

`{p}_emits_k` is one conversion: the whole verified lowering of function
`k` (its `rt` lowering, since `p_fnk()` is computed from `f::program`,
then its emission) inside one budget of 2^20 evaluator steps.
[[native-function-emission-one-statement]] brought a node's cost down far
enough that a hundred-leaf tree of comparisons certifies at about four
fifths of that budget, and left the statement as it was. The ceiling is
still there, a little past a hundred and twenty comparisons, and it is
per function, so the answer to a larger function today is to split it by
hand.

## The design

What `write-elf` did for its certificate
([[native-tool-certificate-budget]], `lib/native/native_build_parts.hthr`,
`crates/cli/src/native/parts.rs`): cut the statement into parts, each
quantified over what came before it.

- A lemma per constructor: the emission of a `Compose` or a `Conditional`
  is the emission of its parts in order, threading the code, the register
  file, the placement's rest and the label counter (as
  `emit_functions_next` threads functions).
- Each part's statement quantifies over the program so far (`(prog) →
  part.emit(prog, file, rest, names) = Emitted(prog ++ code, file', rest',
  names')`), so no part re-reads the code before it, and states the file
  and the counter between parts as literals. The register file is data
  since the round above (`Slots`), which is what makes it statable.
- State the lowered IR as a literal first (one statement: `p_fnk() =
  <literal>`), or every part re-lowers the function from `rt` to find its
  own region.
- The driver cuts where the budget says, as `parts.rs` does: by measured
  steps of an untrusted read, not by a fixed size.

## What a node still costs

The profile of the hundred-leaf tree's emission after the round, largest
first, as shares: the `rt` lowering's type-code checks (`Ty::check`, an
equation of two widths built a successor at a time, about a sixth); the
callee-saved check (`leaves_all`, seven registers against every
instruction, each a `Gpr::same` through two `index` matches, about a
seventh); finding an id among sixteen registers (`File::find_in`, about a
tenth); the rest is spread thin. Each has a cheaper form (a one-pass
`leaves_saved` proved equal to `leaves_all` at `callee_saved()`; an id
index beside the slots), and the first was tried and is not free
([[runtime-shift-conversion-unfolding]], 2026-11-10).

The placement search's read is not under the conversion budget, only
under memory and time (three million steps for the hundred-leaf tree,
where the emission is under one). What is left of it is `NatMap` traffic
(gets, sets and the halving of their keys) and the list appends of
`reads`; it has not been attributed further, and whether it is still
steeper than the function was not measured after the last change.

## Done when

A function of five hundred comparisons certifies under the usual cap, in
parts the driver chose, and no part's statement mentions the code before
it.
