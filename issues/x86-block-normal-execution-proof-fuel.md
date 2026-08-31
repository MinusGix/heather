---
title: Generic normal x86 block execution certificate exhausts kernel fuel
status: open
labels: [compiler,proofs,performance,kernel,x86]
created: 2026-08-30
updated: 2026-08-31
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

## 2026-08-31 partial result

`canonical_execute_block_cons` now provides the small relation-composition
lemma: given a certified tail from the canonical head's normal successor to an
explicit final state, it constructs the certified cons block. Together with
`execute_block_nil`, this scales to the concrete five-instruction `sum4`
lowering at ordinary fuel and removes hand-written `Exists`/`And` trees.

The stronger recursive theorem above still exhausts fuel, so the issue remains
open. A second boundary appeared when a single `refl` was asked to normalize
the complete five-instruction register result. Naming execution stages and
composing their small observation lemmas checks. A complete fix should make
the generic recursive bridge similarly retain sharing instead of repeatedly
unfolding accumulated machine states.
