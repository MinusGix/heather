# A tighter structured x86 lowering — design

Status: **draft 2026-09-29, decisions open (§6).** Owner:
`issues/structured-lowering-code-size.md`. Also lands
`issues/function-ir-x86-fused-compare-branch.md`. Builds on
`docs/native-wc-design.md` §4.5 (near conditionals) and §5.1 (the measurement
that filed this), `docs/function-ir-design.md` (regions and the certified
lowering), `docs/fetched-step-determinism-design.md` §5 (what a new
instruction form owes the step decoder) and `docs/x86-64-execution-boundary.md`.

## 1. What the lowering emits today (V1, measured 2026-09-29)

`field_low` and `field_high` (`lib/field_line.hthr`), lowered at the
placements the three-field tail gives them, encoded with `encode_structured`
and disassembled:

| word | bytes | instructions | `movabs` | `mov` | `cmp` / `setb` / `test` / `je` / `jmp` |
|---|---|---|---|---|---|
| `field_low` | 1,911 | 424 | 97 | 138 | 20 each |
| `field_high` | 2,792 | 603 | 149 | 182 | 30 each |

The words are chains of three shapes.

**A doubling** (`double(x) = x.add(x)`, 32 of them in `raise32`) is 9 bytes:

```text
mov rax, r8 ; add rax, r8 ; mov r9, rax
```

The result never takes the input's register, so every doubling copies in and
out through RAX, and the chain ping-pongs between R8 and R9.

**A mark** (`if state < threshold { state } else { state + weight }`) is
68 bytes:

```text
movabs rax, threshold      10   needed
movabs rcx, 0              10 ┐
cmp    r9, rax              3 │ the comparison's bit, materialised
setb   cl                   3 │ and then tested: 21 bytes where a
mov    rax, rcx             3 │ jcc on the flags is 2
test   rax, rax             3 │
je     false                2 ┘
movabs rcx, 0 ; or rcx, r9 ; mov r8, rcx      16   true arm: a copy of state
jmp    join                 2
movabs rcx, 16 ; add rcx, r9 ; mov r8, rcx    16   false arm
```

**A place** (the same, with `state − threshold + weight` in the false arm) is
84 bytes. Its false arm re-materialises the threshold (10 bytes), because
`mov rax, rcx` destroyed it. In `field_high`, 16 of the 28 places have weight
zero and still spend `movabs rcx, 0 ; add` (13 bytes) adding it.

A mark that reads as a person would write it is 19 bytes, and a place is 18
to 25:

```text
movabs rax, threshold ; cmp r9, rax ; jb join ; add r9, 16          (mark)
movabs rax, threshold ; cmp r9, rax ; jb join ; sub r9, rax ; add r9, 8   (place)
```

Each shape has one cause, and each cause is one lowering capability:

| capability | what it removes | `field_low` bytes saved (estimate) |
|---|---|---|
| **F** branch on the comparison's flags | the materialised bit (21 → 2 a step), and the threshold's re-materialisation it causes | ~540 |
| **P** a result may take a dead input's register; a passthrough arm is empty | the arms' copy-in/copy-out, the copy arm, its `jmp`; a doubling 9 → 3 | ~630 |
| **I** short immediates and a zero | a small weight 13 → 4 or 7; `movabs r, 0` → nothing or `xor` | ~150 |

Together they bring `field_low` to about 600 bytes and `field_high` to about
800, which is 3–3.5× smaller. F's estimate counts the threshold's
re-materialisation as F's to remove, and V5 checks that. Instruction count falls by about the same factor.

**Certificate cost follows the instruction count.** `generate_selected` emits
per instruction a spine definition, a state, an `_execute_from_i` theorem, a
refl step result, and a frame theorem per live value. Leaf `_bytes_are` is
refl, and conversion evaluates every immediate's eight bytes. That is the
round's second payoff: `read_fields_process` sits near its CPU rail, and `tr`
will add code to the same process.

## 2. F: branch on the flags

### 2.1 A condition-code family, not one more jump

The model has three conditional jumps as separate constructors:
`ShortControl::JumpZero`, `NearControl::JumpZeroNear` and `JumpSignNear`.
Each one came with its own bytes, decoder case, rip lemma and AF-commute
lemma. F needs JB and JAE, a signed comparison will want JL and JGE, and
equality JE and JNE. Adding them one at a time repeats that work for every
form.

x86 encodes all sixteen as one family: `70+cc rel8` and `0F 80+cc rel32`.
`cc` names a predicate on the flags, from the manual's table: `B` is CF, `E`
is ZF, `S` is SF, `L` is SF ≠ OF, and each odd code is its even neighbour
negated. So the model gets:

```text
inductive ConditionCode { O, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G }
fn condition_code(cc) → BitVec(4)            // the manual's encoding
fn condition_holds(cc, flags: Flags) → Bool  // the manual's table
ShortControl::JumpIf(cc, displacement: BitVec(8))     // 70+cc rel8
NearControl::JumpIfNear(cc, displacement: BitVec(32)) // 0F 80+cc rel32
```

There is one rip lemma per width (`jump_if_taken_rip`/`not_taken`, taking
`condition_holds`) and one AF-commute lemma, since no condition code reads
AF. The step-form decoder gains two byte ranges, not sixteen cases:
`decode_plain_form` for `0x70–0x7F` and `decode_two_byte_form` for
`0x80–0x8F`.

`JumpZero`, `JumpZeroNear` and `JumpSignNear` become `JumpIf(E, _)`,
`JumpIfNear(E, _)` and `JumpIfNear(S, _)`. They must be migrated rather than
kept beside the family: the step decoder has to read byte `0x74` as exactly
one form. The migration is about 150 lines in 15 files (library, generators,
tests). §6 Q1 asks whether it goes in this round.

### 2.2 The fused branch in `StructuredCode`

Today `CodeBranch(register, yes, no)` means `test r, r; jz no; yes; jmp join;
no`. The branch computes its own flags (`structured_test`), so no flag is ever
live across an artifact boundary. That property is worth keeping: flags stay
out of `StructuredArtifact`, and the CMP lives *inside* the branch too.

```text
inductive BranchTest {
    NonZero(register: Gpr),                 // test r, r ; j(E) false
    Compare(left, right: Gpr, cc: ConditionCode),   // cmp l, r ; j(¬cc) false
}
CodeBranch(test: BranchTest, yes, no)      // and CodeBranchNear
```

`structured_test` becomes `branch_holds(test, state)`. For `Compare` that is
`condition_holds(cc, sub_flags(l, r))`. The lemma
`unsigned_lt_bit(l, r) = condition_holds(B, sub_flags(l, r))` is refl, because
`sub_flags.cf` is `borrow_sub_bit` and `unsigned_lt_bit` is defined as that
(bitvec.hthr:769). V2 checks this at open operands. §6 Q2 is whether to
generalise the constructor like this or add a pair beside it.

**Lowering.** A `Conditional` whose condition port is produced by an
`UnsignedLessThan` (or `SignedLessThan`) node in the immediately preceding
`Sequence` prefix, with no other consumer, is selected as `Compare`. The
comparison node leaves the prefix DAG, and its operands stay live into the
branch. If anything else reads the bit, the materialised rule stays, as
`function-ir-x86-fused-compare-branch` requires.

### 2.3 A one-armed branch

With an empty true arm (§3 makes the passthrough arm empty), `cmp ; jae no ;
jmp join ; no: …` still spends the `jmp`. The layout should be `cmp ; jb join
; no-arm ; join`. That is `CodeWhen(test, body)`: run `body` unless `test`
holds, with bytes `test ; j(cc) join ; body`. This is an explicit constructor,
so that bytes remain a function of the constructor and never depend on
whether an arm happens to be empty. The lowering uses it when one arm is
empty. If the empty arm is the false one, it negates `cc`, which the family
makes free.

## 3. P: results in place

`lower_dag` refuses to let a temporary coincide with an input
(`InputOverlapsTemporary`, function_ir_x86_lower.rs:2698) and requests every
region's output in a fresh register. `issues/native-loop-state-in-place.md`
(closed) solved the same problem for the record loop's carry only.

The rule: **a node's output may take the register of an input that is dead
after it and not protected.** The protected set is the caller's `keeps` (R11
and R13–R15 for the field words). A doubling then becomes `add r, r`, and a
chain of steps keeps its state in one register. For a `Conditional`, the join
register is the state's own register. The arm that passes the state through
is then empty and needs no code, and §2.3 drops its jump.

The frame facts change shape but not kind. The overwritten input stops being
a live value at that instruction, so it gets no `preserves` theorem there. A
protected register is never chosen, so `Protected` proofs are unchanged. What
this needs from the allocator is per-node liveness inside a DAG, and whether
each region's inputs are live after it. `select_here` already computes
`next_inputs` for a `Sequence`'s continuation. V4 checks whether the
`Compose` boundary of a helper call (`double` is a helper) forces a move of
its own.

Two copies remain after P: a protected entry input moved into a working
register (`mov rax, r11`, 3 bytes, once per word), and a genuine copy where
two consumers need a value. The reflector spells a copy as `Const 0` plus
`BitOr` (function_ir_source/structured.rs:382), because FunctionIR has no
copy node. I recommend lowering `Const 0` as `xor r, r` (§4) and leaving the
IR alone, which makes a copy 6 bytes. `BitOr(0, x)` should not be matched as
a `mov`, because that is a special case keyed on shape rather than value.
§6 Q3.

## 4. I: short immediates

New ordinary `Instruction` forms. Each costs the same list: `canonical_bytes`
and `canonical_length`, `execute_register`, `Execute`,
`erase_af_normal_commute`, the reference decoder and its completeness,
`decode_step_form` and `ordinary_form_complete`, and on the Rust side the
enum, encoder and step renderer.

| form | bytes | used for |
|---|---|---|
| `AddRI8(r, imm8)` / `SubRI8` | `REX.W 83 /0 ib`, `/5 ib`: 4 | weights below 128 |
| `AddRI32(r, imm32)` / `SubRI32` | `REX.W 81 /0 id`, `/5 id`: 7 | weights below 2^31 |
| `MovR32I(r, imm32)` | `B8+r id` (REX.B for R8–R15): 5 or 6 | constants below 2^32 (zero-extends) |
| (existing) `XorRR(r, r)` | 3 | the constant zero |

The immediates are **sign-extended** to 64 bits by the hardware.
`issues/function-ir-x86-constants.md` flagged this. The semantics must be
stated with `sign_extend`, and the lowering picks a form only when the
extended value equals the constant (`imm8` for −128…127, `imm32` for
−2^31…2^31−1). A weight of 2^31 must stay `movabs`. A mutation test should
refuse a certificate that uses `imm32` for such a constant.

The thresholds (all at least 2^32) stay `movabs`. They are genuinely 64-bit.

`x + 0` is not folded by the lowering. `field_high`'s zero weights are a
source choice (`place(…, 0)` states "take the top digits away, weigh them
nothing"). An `add r, 0` costs 4 bytes after I. Folding is a DAG
simplification with its own certificate story, filed separately if wanted.

## 5. Out of scope, filed

- **Shifts.** `raise32` is `shl r, 32` (4 bytes), against 96 after P. FunctionIR
  already has `ShiftLeft`, but the x86 model has no SHL, and SHL leaves OF and
  AF undefined for counts above 1 (a second `∃` beside TEST's AF). The source
  would also have to say `shift_left(8)` rather than `times256`, and
  `decimal_line`'s `bv_omega` proofs unfold `times256` into doublings. That
  is a library change with its own proof work.
- **One formatter copy shared by a call** instead of three inline copies
  (`docs/native-wc-design.md` §8 Q4's other alternative).
- **Constant folding** (`x + 0`, `x | 0`) in the DAG.

## 6. Decisions for the user

1. **Migrate `JumpZero`/`JumpZeroNear`/`JumpSignNear` into the family in this
   round?** *Recommended: yes, as slice F's first commit.* The decoder cannot
   have two readings of `0x74`. The alternative, a family that skips E and S,
   leaves a hole in the table that every later reader has to learn about.
2. **Generalise `CodeBranch` over a `BranchTest`, or add a
   `CodeCompareBranch` pair beside it?** *Recommended: generalise.* Every
   later condition would otherwise add two constructors times five folds.
   The 26 lines that name them today become `CodeBranch(NonZero(r), …)`.
3. **A copy: `xor` + `or` (6 bytes, no IR change) or a FunctionIR `Move` node
   (3 bytes, `lib/function_ir.hthr` and its consumers)?** *Recommended: `xor`
   now.* After P, copies are rare in these words.
4. **Order.** *Recommended: F, then P, then I.* F lands the family and removes
   the most per step. P's empty arms need F's negated jumps (§2.3). I is
   mechanical and independent, and could run in parallel on its own branch.
5. **Does the round take on shifts (§5)?** *Recommended: no.* After P a
   doubling is 3 bytes, and the shift is a library-proof round.

## 7. Probes, before this design is final

- **V1** (done, §1): the byte and instruction breakdown.
- **V2**: `condition_holds(B, sub_flags(l, r)) = unsigned_lt_bit(l, r)` by
  refl at open `l, r`, and the same for `L`/`signed_lt_bit`.
- **V3**: the size of the migration (Q1). Is the family's
  `decode_step_form` and `ordinary_form_complete` coverage mechanical? Do the
  loop certificates that name `JumpZeroNear` re-check unchanged apart from
  spelling?
- **V4**: allocate `double(double(x))` in place. Does the `Compose` boundary
  force a move, and does the frame generator accept an overwritten dead input?
- **V5**: why the place's false arm re-materialises the threshold: only
  `mov rax, rcx` clobbering RAX, or does an arm re-emit its `Const` nodes
  anyway? If the latter, a constant port carried into an arm is part of F.

## 8. Acceptance

- `field_low` and `field_high` each at most 40% of today's bytes (1,911 and
  2,792), with the instruction histogram recorded as §1's table is.
- `field_low_certifies`, `field_high_certifies`, `native_wc` and every
  structured/recursive lowering test pass. The tests pinning the old sequences
  (`comparisons_use_a_safe_zero_cmp_setcc_sequence`, the displacement
  arithmetic in `function_ir_recursive.rs`) are rewritten to pin the new ones.
- Negative controls: a branch with the wrong `cc` is refused; an `imm32`
  whose sign extension differs from the constant is refused; an in-place
  result that overwrites a protected or still-live register is refused.
- The materialised comparison still lowers where the bit has another
  consumer, with a test.
- `scripts/perf ab` on the field-word certificates and the `wc` build: the
  counters move with the instruction count, and the seconds are reported
  apart from them. This round names performance, so it measures.
