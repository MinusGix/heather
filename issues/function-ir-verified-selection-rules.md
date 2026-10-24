---
title: Bring the immediate and compare-and-branch forms into the verified lowering
status: closed
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-23
updated: 2026-10-24
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

## Log

### 2026-10-24: all four landed, as cases of the one theorem

- **The file knows values.** `File` gains `known: List<Known>`
  (`Constant(id, value)`, `Compared(id, op, left, right)`) and
  `Represents` is the register half and `KnownHold`. Lookups
  (`known_value`, `known_comparison`) carry soundness lemmas; joins keep
  the entry file's facts (`File::meet(.., known)`), so nothing an arm
  learns leaks past the join.
- **Placement says what folds.** A placement entry is `Place::Into(r)` or
  `Folded`. A folded `Const` is only recorded; a folded comparison records
  its operands. The planner folds a constant whose every read is an ADD
  operand and fits an immediate, and a comparison read once, as a branch
  condition, last in its block (`StructuredRegion::folds`). As before a
  wrong placement is a refusal: an id nothing holds and nothing knows is
  not found.
- **Immediates.** `File::add` takes a known constant as `AddRI8`/`AddRI32`
  (either operand, ADD commutes); the fit is `add_immediate`, an
  evaluated `sign_extend(ofNat(c)) == ofNat(c)` with
  `BitVec::eq_of_eq_bit` as its lemma. A known constant read by anything
  else is loaded with `MOV r, imm64` where it is read.
- **Compare and branch.** `x86_64_asm_runs` has `Test` (`Nonzero(r)` =
  TEST/JE, `Compare(cc, l, r)` = CMP/Jcc) and `Site::runs_branch_on`;
  `x86_64_stack_runs` has `moves_branch_on`. `File::branch_test` picks a
  bit register when there is one, else a known comparison's CMP with the
  failing condition (`CompareOp::fails`: AE, GE, NE).
- **The move after a call.** `Move` joins the in-place rule: a move whose
  source dies there takes the source's register and costs nothing. In a
  body that calls, RAX is allowed for that only when the output is not
  read after a later call (`StructuredRegion::crossing`), so a call's
  result is used where it lands. The reflector is unchanged.
- **Round 1's leftovers.** A `Move` already in place is a retag
  (`copy_found`), and a commutative op whose right operand is in the
  destination is `OP d, left` (`BinaryOp::swap`).

Sizes on `examples/x86-native/branches.hthr` (certified program bytes,
`ret` included; the old path at 82521ea measured as body + 1):

| | old | before | after |
|---|---|---|---|
| nested_true / _false | 59 | 83 | 65 |
| unsigned_threshold | 30 | 54 | 45 |
| take_threshold | 33 | 57 | 48 |
| nudged | 64 | 93 | 60 |
| composed | 75 | 93 | 84 |
| keep_twice | 51 | 248 | 227 |
| either | refused | 268 | 223 |

What is left of the gap is not selection: every function's 8-byte frame
pair, even a leaf's ([[function-ir-verified-leaf-frame]]), near jumps
where the old path used rel8 ([[function-ir-verified-short-jumps]]; 7
bytes for each one-armed conditional), and eight spills and reloads per
call ([[function-ir-verified-live-spills]], all of `keep_twice`'s
excess). Net of the first two, every leaf example is at or under the old
size.
