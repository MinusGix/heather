---
title: Lower FunctionIR's pure regions by a Heather function proved correct once
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-21
updated: 2026-10-21
---

Round S4 of `docs/native-program-logic-design.md` (§3.2, §9): lower
FunctionIR's pure regions to x86 by a Heather function whose correctness is
one theorem, replacing the per-function certificate path (Rust lowering,
`heather_emit`, the structured and control-block certificates).

## Scope

- `lower : CheckedRegion → Prog` (or code with a contract) in Heather, with
  register placement as part of it or as a checked input.
- One theorem: the lowered code computes the region's meaning, as a
  `Proved` contract (outputs in their registers, scratch named, the rest
  kept).
- The `examples/x86-native` pure examples (branches, calls, composition,
  sharing, stack) built through it, after which burn B2 can start.

## What it assumes from elsewhere

- Nothing first (design §8: S4 is an input to S3's `Proved` regions and to
  B2, and waits on no round). The theorem is stated as its own contract;
  **[[native-one-wp]]** owns `Proved` and `Wp`, and its `Proved` item takes
  this contract when S2 lands. Conditionals are the one place the rounds
  below touch jumps; see round 2.
- **[[in-language-certificate-emission]]** and
  **[[generators-in-the-language]]** own how a Heather metaprogram is run by
  the compiler; this issue assumes only that `lower` can be evaluated.

## Rounds

The lowering is split so that **register allocation sits outside the proof**.
`lower` takes a placement (a destination register per node) from anywhere —
a Heather heuristic, or Rust's allocator as untrusted input — and tracks an
abstract register file (`Gpr → Option<Port>`: which value each register
holds) while it emits. An operand is read from a register the file says
holds it; a destination that would clobber a value still needed makes a
later lookup fail, so `lower` returns `None`. The theorem is over every
placement: whenever `lower` returns code, the code is right. A bad placement
costs a refusal, never a wrong program.

1. **Straight-line dataflow regions.** `lib/function_ir_lower.hthr`:
   `Represents(file, values, gprs)` (64-bit values as themselves, 1-bit
   values zero-extended, as `ValuePlaced`/`BitValuePlaced` do today),
   instruction selection per node (Add/Sub/And/Or/Xor as `OP d, b` or
   `MOV d, a; OP d, b`; Const as `MOV d, imm`; comparisons as
   `XOR d, d; CMP a, b; SETcc d`; Move as a `MOV` or nothing), outputs
   moved to their registers through the same file, and one theorem:
   inputs represented and `RegionHolds` give outputs represented after
   `execute_block_normal(code, s)`, memory and `rip` as the block's, every
   register the code does not write unchanged. Shifts and other widths are
   refused (no instruction in the ISA model yet). Done when `add64`,
   `sum4` and `mix`'s region lower through it by evaluation, with a
   clobbering placement refused as a negative control, and a Heather
   placement heuristic produces the placements.
2. **Conditionals** (`StructuredRegion`'s `Conditional`, `Sequence`,
   `Compose`): code as a `Prog` with `Jcc`/`Jmp` to labels, proved over
   the assembled bytes. This is where S2's `Wp` (its `Jcc`/`Jmp`
   obligations) would be the natural tool; if S2 is not there yet, the
   round proves the pure, syscall-free fragment of it it needs and S2
   generalises it. `branches.hthr` through it.
3. **Calls and the stack** (`calls`, `composition`, `sharing`,
   `stack_local`, `stack_save`, …): a callee's contract as a `Proved`-shaped
   item, the frame view, spills.
4. **The CLI through the compiler**: `compile-x86` evaluates `lower` and
   instantiates the theorem instead of generating a certificate per
   function; the immediate forms (`AddRI8`/`AddRI32`, CMP-and-Jcc without a
   materialised bit) come back as selection rules with their own cases in
   the theorem. Then B2 can start.
