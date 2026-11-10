---
title: Settle a narrow value only where its upper bits are read
status: open
labels: [compiler,function-ir,x86,optimization]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-10
---

The verified lowering holds a value narrower than 64 bits in one of two
kinds (`lib/native/function_ir/function_ir_lower.hthr`, "Narrow widths"):
`Narrow(w)`, zero-extended, and `Low(w)`, where only the low `w` bits are
the value. An ADD, a SUB or a left shift produces `Low`, and today each is
settled at once, by `SHL r, 64-w; SHR r, 64-w`, so every node's output is
`Narrow`. That is two instructions after every carrying operation:
SHA-256's `T1` (`lib/native/crypto/sha256_round.hthr`) settles four sums
in a row where one settle after the last would do.

The kinds already say what is sound. A node's operands may stay `Low` when
the node reads only their low bits:

- ADD, SUB, AND, OR, XOR and a left shift of `Low` operands give `Low`
  (`BitVec::resize_add`, `resize_sub`, `resize_shift_left` and the bitwise
  laws in `lib/std/bitvec/bitvec_resize.hthr` are stated for exactly this:
  the low bits of the wide operation are the narrow operation).
- A right shift, an unsigned comparison, an equality, a widening resize, a
  region's output and a call's argument read the upper bits, so they need
  `Narrow` and settle an operand that is `Low`.
- A narrowing resize of a `Low(w)` to `v ≤ w` is a retag.

## Scope

- `Node::lower` takes operands at either kind and settles on demand, with
  the planner choosing where (a value read `Narrow` twice is settled once,
  at its definition).
- A left shift by `k` followed by its settle is one `SHL r, 64-w+k` and one
  `SHR r, 64-w`: fuse them.
- When the machine model has 32-bit operand forms
  ([[x86-narrow-and-rotate-forms]]), `w = 32` settles for free and these
  rules only matter at the other widths.

## Done when

`sha256_t1` settles once per value that is shifted right or returned, its
certificate still checks, `crates/linked`'s tests pass on the regenerated
assembly, and the byte counts before and after are in this issue's log.

## What it assumes from elsewhere

- **[[function-ir-narrow-arithmetic]]** owns the kinds and what is still
  refused (signed comparison, arithmetic shift, sign extension).
