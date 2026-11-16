---
title: Settle a narrow value only where its upper bits are read
status: open
labels: [compiler,function-ir,x86,optimization]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-14
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

## Log

- 2026-11-14: At width 32 the settle is now one instruction: `settle_code` writes `MOV r32, r32` of the register onto itself (`MovSelf32`, which clears the upper half as every 32-bit destination's is) where it wrote `SHL r, 32; SHR r, 32`, proved by `mov_self32_resize` (the move's value is `x.resize(32).resize(64)`) inside `in_place_settle`. That covers every settle at 32: a sum, a difference, a left shift and a word narrowed to 32 bits. Every other width keeps the shift pair (`settle_shifts`), so the lazy settling this issue describes still matters there, and at 32 it would now save one move per chain rather than two shifts. Probes: `add32_code`, `left_shift32_code`, `narrow_word_code` and the 16-bit control `add16_code` in `lib/_tests/native/function_ir/function_ir_rotate_tests.hthr`.
- 2026-11-14: Measured after `scripts/linked` (`scripts/bench-native --quick --no-compile`, callgrind, per SHA-256 block): 79,955 to 77,691 instructions; shifts 14,032 to 9,504, register moves 14,493 to 15,685 (the new moves are the settles). `sha256_t1` is 210 bytes to 145; its certificate checks. Each rotation still has one settle after its left shift until the optimizer rewrites the pair into `RotateRight`, and each 32-bit sum one move, which a 32-bit `ADD` would remove ([[x86-narrow-and-rotate-forms]]).
