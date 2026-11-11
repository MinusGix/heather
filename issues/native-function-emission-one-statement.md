---
title: A function's emission is one kernel statement, which bounds how large a compiled function may be
status: closed
labels: [native,compiler,performance]
area: heather-in-heather
milestone: [nh-front,self-lexer]
created: 2026-11-10
updated: 2026-11-10
---

What `compile-x86` can certify is bounded by its largest *function*, and
since the round that closed [[compile-x86-certificate-memory]] and
[[runtime-generator-program-size]] by one thing: the function's emission.
A program's size is not bounded by anything measured (the scanner's
automaton, `scan_step`, is twenty-six functions and about fifteen thousand
bytes in one certificate).

## The statement

`{p}_emits_k` (`crates/cli/src/native/verified.rs`) says that emitting
function `k` onto the code before it leaves the code, the placement and the
label counter the certificate states as literals:

```heather
theorem p_emits_k(): EmitsAs(p_fnk().emit(p_code_j(), k, p_rest_j(), labels), p_code_k(), p_rest_k(), names) { refl }
```

It is one conversion, so the whole verified lowering of the function runs
inside one budget of `DEFAULT_FUEL` (2^20) evaluator steps. Measured on the
cloud box at width one, each function a single `runtime fn` of constants
under comparisons of its argument:

| shape | emission steps | result |
|---|---|---|
| 16-arm `else if` chain | 0.29M | certifies |
| 24-arm chain | 0.49M | certifies |
| 40-leaf balanced tree | 0.69M | certifies |
| 40-arm chain | past 2^20 | `…_emits_0: OutOfFuel` |
| 64-leaf balanced tree | past 2^20 | `…_emits_0: OutOfFuel` |

So roughly fifty comparisons in a tree and thirty-five in a chain: a chain
costs more per arm, growing a little faster than linearly in its depth.
The scan of the same functions (`{p}_scanned_k`) is a third to a half of
the emission and no longer the first limit ([[function-ir-scan-id-cost]]).

Until the round that filed this, `EmitsAs` was three equations (the code,
the placement, the counter), each its own `refl`, and each evaluated the
emission again: nothing one conversion computes is kept for the next. It is
one equation now (`Emitted::emission`), which cut a certificate's largest
cost to a third without moving this limit.

## The memory beside it

The untrusted reads of one function (its placement, then its emission) are
each one evaluation in a fresh arena. A 40-leaf tree compiles at a peak of
about 1.4 GB and a 64-leaf tree reads at about 3.6 GB before its emission
statement is refused (the generator, run alone on the 64-leaf function,
peaks at about 1.2 GB). That growth is steeper than the function's size and is not
attributed between the two reads. The placement planner had exactly this
shape before (a `let` read at several places is computed at each,
[[elaborated-let-sharing-lost]]; it now binds with `shared`), and the
emission (`StructuredRegion::emit`, `function_ir_lower_structured.hthr`)
has not been read for the same pattern. `File::meet`, the join of two
arms' register files, is a closure over both files and is the first
suspect for the chain's superlinear steps.

## Directions

- **Emit a region at a time.** The emission of a `Compose` or a
  `Conditional` is the emission of its parts in order, threading the code,
  the file, the placement and the counter. A lemma per constructor
  (`emit_compose_next`, as `emit_functions_next` is for functions) would let
  the certificate state each part's result as a literal and glue them, so
  the budget bounds the largest basic region, not the function. The
  literals between regions include the register file, which the certificate
  does not state today.
- **Share what the lowering binds.** Whatever `emit` computes in a `let`
  and reads twice is computed twice by the kernel; `shared` (or the
  language fix, [[elaborated-let-sharing-lost]]) removes it at the source.
  The proofs about `emit` unfold through `shared` by δ and β.
- **Tables instead of chains.** Most functions this large are a table
  written as comparisons, and [[rt-fixed-arrays-and-tables]] removes the
  shape itself.

## Done when

A function of a hundred comparisons certifies under the usual cap (the
64-leaf tree and the 40-arm chain above are the first two cases), or the
reason it cannot is written here with the shape that does; and the read
memory is attributed.

## Log

- 2026-11-10: Closed by the round that attributed it. The statement is still one
  conversion; what changed is what a node costs inside it, and the memory.

  **Attribution.** Emission was linear in the function all along (about
  3,500 steps a node at the start of the round). The memory was not the
  emission's read: the placement search's read grew quadratically (its
  liveness was lists of ids, scanned and re-concatenated at every node) on
  top of a flat 1.1 GB for the generator, and the emission's read is some
  tens of megabytes. The superlinear steps of a chain were number
  comparisons, not `File::meet`.

  **What was costing the steps**, in the order found:

  - `Nat::eq_dec` walked both numbers a successor at a time. It decides by
    `same` now (which the kernel iterates over runs) and reads its proofs
    off `same`'s two laws.
  - A counter written a piece at a time (`next`, then `Succ(next)`, read
    off a call's result) was compared a successor at a time by every
    comparison, however the comparison's step classified, which made every
    id lookup linear in the id and the function quadratic
    ([[succ-chain-numbers-fold-unary]], a kernel evaluator change).
  - The register file was a function (`Gpr → Option<Held>`): a lookup
    walked every write since the last join, and a join re-evaluated both
    arms' files per register. It is sixteen slots of data now (`Slots`,
    `slots_at`, `slots_set`), with the two laws the proofs read
    (`File::write_at`, `File::meet_at`).
  - The placement search keeps counted sets (`Reads`, a `NatMap` of
    counts) where it kept lists, with the same answers: the linked SHA-2
    and scanner code is byte-identical (`scripts/linked --check`).

  **Measured** (cloud box, width one, fresh salts, the usual 8 GiB cap):

  | shape | before | after |
  |---|---|---|
  | 40-leaf tree, emission steps | 0.70M | under 0.39M |
  | 40-leaf tree, placement read steps | 4.3M | under 1.7M |
  | 40-leaf tree, peak | 1.9 GB | 1.1 GB |
  | 40-arm chain | `OutOfFuel` | certifies, 8 s, 1.4 GB |
  | 64-leaf tree | `OutOfFuel`, 3.6 GB | certifies, 8 s, 1.2 GB |
  | 64-arm chain | `OutOfFuel` | certifies, 14 s, 2.9 GB |
  | 100-leaf tree | `OutOfFuel` | certifies, 39 s, 2.1 GB (`emits_0` 0.83M steps, `scanned_0` 0.40M, `returns` 0.24M; placement read 3.0M) |

  So the done-when holds with the statement as it is, at about four fifths
  of the budget for the hundred-leaf tree. That margin is not a design:
  [[native-function-emission-in-parts]] is the part of this issue's
  directions that removes the ceiling, and it lists what a node still costs.
  Past a hundred comparisons the first refusals are now the generator's, not
  the emission's ([[runtime-generator-large-function-limits]]).

  **Tried and taken back out.** `Nat::equation` deciding by `same` and
  walking only when its proof is transported: it cost an open-term proof
  (`rt_lower_tests::spread_agrees`) a quarter more steps. Deciding the
  lowering's type-code checks by `Ty::same` (no proof kept): it removes the
  equation's share of the emission, about a sixth, and made the smaller
  agreement probes two to three times cheaper, but put `spread_agrees`
  past its budget again, for a reason found this time
  ([[runtime-shift-conversion-unfolding]], its 2026-11-10 log).

  **Gotcha met on the way.** With the file as data, one proof's `match`
  lost its synthesized motive: the goal's stuck head now takes more than
  `STUCK_SPELLING_STEPS` to spell, and the fallback is the unabstracted
  goal, so the error is a `trivial` mismatch far from the cause. The motive
  is written out there (`StructuredRegion::emit_calls_runs`, the `Conditional` arm);
  [[match-motive-stuck-spelling-budget]].
