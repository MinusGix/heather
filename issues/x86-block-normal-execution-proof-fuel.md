---
title: Generic normal x86 block execution certificate exhausts kernel fuel
status: open
labels: [compiler,proofs,performance,kernel,x86]
created: 2026-08-30
updated: 2026-08-30
---

The first typed x86 block layer defines both:

```text
execute_block_normal : List<Instruction> -> MachineState<M> -> MachineState<M>
ExecuteBlock         : List<Instruction> -> MachineState<M> -> MachineState<M> -> Type
```

`ExecuteBlock` chains the canonical relational `Execute`, preserving TEST's
undefined-AF choice. `execute_block_normal` chooses the existing functional
representative. The expected generic bridge is:

```text
execute_block_normal_is_allowed(instructions, before):
    ExecuteBlock(instructions, before,
        execute_block_normal(instructions, before))
```

The structurally recursive proof packages each intermediate state in an
`Exists`, uses `canonical_execute_normal_is_allowed` for the head, and recurs
on the tail with the computed state. Its declaration is kernel-refused with
`OutOfFuel` at the ordinary budget after the block definitions themselves
check.

The concrete two-instruction `MOV RAX,RDI; ADD RAX,RSI` certificate checks and
is the accepted first FunctionIR lowering slice. Specializing the theorem at
each block is not the desired general API, but it avoids blocking that slice
while preserving the authoritative relational semantics.

## Acceptance

- The generic bridge checks at ordinary fuel.
- It covers instructions with relational choice, not only the deterministic
  MOV/ADD subset.
- A mutation choosing an inadmissible intermediate/result state is refused.
- No global fuel increase is used as the fix.

Investigate theorem spelling, named intermediate families, projection
annotations, and whether a small relation-composition lemma prevents the
recursive goal from repeatedly unfolding the complete x86 state and
instruction semantics. Measure the failing conversion before changing the
kernel.
