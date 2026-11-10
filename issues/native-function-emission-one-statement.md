---
title: A function's emission is one kernel statement, which bounds how large a compiled function may be
status: open
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
