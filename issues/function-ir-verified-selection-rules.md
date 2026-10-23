---
title: Bring the immediate and compare-and-branch forms into the verified lowering
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-23
updated: 2026-10-23
---

[[function-ir-verified-lowering]] round 4 routed `compile-x86` through
`lower_program` and left out the selection rules it named. Each one needs
its own case in the theorem. Until they land, the verified path emits code
that is correct but longer than the per-function path's:

- **Immediates.** Today a `Const` is `MOV r, imm64` and its use is
  register to register. `AddRI8`/`AddRI32` (sign-extended) take an operand
  known to be a small constant. Two pieces are needed: the file has to know
  the constant (the representation invariant gains `values(id) =
  ofNat(c)`), and the lowering must not materialise a `Const` whose only
  uses are immediates. The fit check should be an evaluation (`sign_extend(
  ofNat(c)) == ofNat(c)` as a Bool and its soundness lemma), not
  arithmetic on an open `c`. `branches.hthr`'s `nudged` is the example; its
  test used to require `AddRI8(` and `AddRI32(` in the certificate.
- **Compare and branch.** A `Conditional` on a comparison materialises the
  bit (`XOR; CMP; SETcc; TEST; JE`). The rule is CMP and Jcc on its flags,
  when the bit has no other use. `Site::Runs` needs a branch lemma on a
  flag.
- **The move after a call.** The reflector moves every call's result out
  of RAX into a fresh id at once, so the planner never leaves it there.
  That costs one MOV per call, and a dead one when the result is used
  once, at once.
- Round 1's leftovers: `MOV r, r` for a `Move` already in place, and
  `OP d, b` into the right operand's register for commutative operations.

## What it assumes from elsewhere
- **[[function-ir-verified-lowering]]** owns the theorem and the planner.
  Assumed here: only that every rule is a case of `lower_program_correct`,
  never a per-program proof.
