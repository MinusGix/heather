# A tighter structured x86 lowering — design

Status: **decisions taken 2026-09-29 (§6, all as recommended); probes V2–V5 done 2026-09-29 (§7.1); slice F landed 2026-09-30 (§2.4), F′ the same day (§2.5). P next, then I.** Owner:
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
| **F** branch on the comparison's flags | the materialised bit (21 → 2 a step) | ~380 |
| **F′** a constant the comparison loaded stays live into the arm (V5) | the threshold's second `movabs` in a place's false arm | ~160 |
| **P** a result may take a dead input's register; a passthrough arm is empty | the arms' copy-in/copy-out, the copy arm, its `jmp`; a doubling 9 → 3 | ~630 |
| **I** short immediates and a zero | a small weight 13 → 4 or 7; `movabs r, 0` → nothing or `xor` | ~150 |

Together they bring `field_low` to about 600 bytes and `field_high` to about
800, which is 3–3.5× smaller. Instruction count falls by about the same factor.

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

`JumpZero`, `JumpZeroNear` and `JumpSignNear` stop being constructors and
become functions: `JumpZeroNear(d) = JumpIfNear(E, d)`, and likewise for the
other two. They can't stay beside the family as constructors, because the
step decoder has to read byte `0x74` as exactly one form. Clients only ever
*construct* these forms (no `match` outside `x86_64_block`), so the functions
keep every client library and generated certificate textually unchanged. V3
shows the family is definitionally the old forms, so their proofs re-check.
The edits fall in the control layer: `x86_64_block`, `x86_64_step_forms`,
`x86_64_fetched_code`, `x86_64_structured_block`, `x86_64_access_code`, and
the Rust encoder.

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

### 2.4 As landed (2026-09-30)

Three commits:

1. **The condition-code family** (`x86_64_block`, `x86_64_step_forms`),
   as §2.1 describes. No client changed.
2. **`CodeBranch` over a `BranchTest`** (`x86_64_structured_block`, the
   shared helpers in `x86_64_fetched_code`, `AccessBranch`'s callers).
   `branch_test_state` is a record literal whose RIP, registers and memory
   don't depend on the test, so the fetched-code arithmetic reads off for an
   open test. At `NonZero(r)` it is `structured_test(r, …)`, so no loop
   proof changed. Where TEST's length used to reduce, the proofs now go
   through `branch_test_bytes_len` and a transport by `branch_test_canonical`.
3. **The fused lowering.** Fusion lives in the x86 lowering, not in the
   shared IR: `StructuredRegion` is unchanged, and a `Sequence` whose prefix
   ends in the comparison becomes the plan `FusedSequence`. That plan is an
   operand DAG (the prefix minus the comparison, computing the one operand
   the prefix owns) followed by a `Conditional` testing `PlannedTest::Compare`.
   The certificate reuses `emit_sequence` over the operand region and a copy
   of the `Conditional` whose inputs are the two operands, so their placement
   facts come for free. The bit is a named `_test` Boolean over the operands'
   values, and `unsigned_compare_skips` / `signed_compare_skips` tie
   `branch_skips` to it. The materialised rule stays for every other shape:
   two inputs compared, two computed operands, a narrower width, or the bit
   read anywhere else.

Measured the same way as §1: `field_low` 1,911 → 1,534 bytes (424 → 345
instructions) and `field_high` 2,792 → 2,225 (603 → 484). Every step is now
`cmp r, r ; jae`, which is F's share of the §1 estimate.

Tests: the plan interpreter runs a fused unsigned plan (from source) and a
signed one (hand-built, with the constant on the left) at the values either
side of the constant and at the signed extremes. Both certify, and each
refuses a code that tests the other condition or swaps the operands.
`unsigned_threshold` also runs natively in `native_branches` against C. The
reflector reads no signed condition from source yet ("Boolean values require
an input, constant, or `unsigned_lt_bit`"), so the signed fused path is
covered by hand-built regions only.

### 2.5 F′ as landed (2026-09-30)

The reflector rewrites the region where it builds a conditional
(`share_compared_constant`, beside `fusable` in the x86 lowering), so the
selector, the certificate and the source expansion all see the same region.
The rewrite applies when the prefix is fusable, its computed operand is a
lone `Const`, both arms are dataflow, and an arm loads the same constant again
for a node to read. The prefix then outputs the constant's port as well as
the bit, the conditional passes the port to both arms, and the arm's own
`Const` is dropped, with its readers renamed to the port. `fusable` accepts
the computed operand as a second prefix output. The fused plan already
carried that operand's register into the branch, so selection and the
certificate needed no change: the arm's placement fact for the port is the
one the operand DAG proves. A constant an arm returns as it is stays that
arm's own load, since a dataflow output cannot be an input.

`field_low` 1,534 → 1,374 bytes (345 → 329 instructions) and `field_high`
2,225 → 1,945 (484 → 456): one `movabs` fewer a place, and `sub r, r10` in
place of `movabs rax, t ; sub r, rax`.

Tests: `take_threshold` (`a < 2^32 ? a + b : a - 2^32 + b`). Its reflected
false arm reads the prefix's port and loads nothing, the plan interpreter
agrees at the edges, and the source expansion checks. With the arm reading
`b` there instead, the expansion is refused. Its certificate checks, loads
the constant once, and refuses a false arm claiming to take away `b`. It
also runs natively in `native_branches` against C. A unit test pins where
the rewrite does not apply: another constant, an arm that returns the
constant, and a narrow comparison.

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

## 6. Decisions (2026-09-29, with the user: each as recommended)

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
4. **Order.** *Recommended: F, then P, then I* (F′ after F, V5). F lands the family and removes
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

### 7.1 Results (2026-09-29)

Each probe was checked with the release CLI under the usual caps. The two
library probes each had a mutated control that the kernel refused
(`NotConvertible`).

**V2 holds.** With `condition_holds` written out from the manual's table,
`condition_holds(B, sub_flags(l, r)) = l.unsigned_lt_bit(r)`,
`condition_holds(L, sub_flags(l, r)) = l.signed_lt_bit(r)` and
`condition_holds(AE, …) = !l.unsigned_lt_bit(r)` are all `refl` at open
`l, r`. `sub_flags` states CF as `borrow_sub_bit`, SF as the difference's
sign bit and OF as `signed_overflow_sub`, which are the library's
definitions. `negate_holds` (`condition_holds(negate(cc), f) =
!condition_holds(cc, f)`) is sixteen cases: each is `refl` or `sym(not_not)`.

**V3 holds, and the migration is smaller than feared.** Defined beside the
old forms, the family is definitionally the old forms at E and S. Short and
near bytes, and short and near RIP (`JumpIf(E, d)` against `JumpZero(d)`,
`JumpIfNear(S, d)` against `JumpSignNear(d)`), are all `refl` at an open
state and displacement. A sixteen-entry opcode table (`short_cc`, one
`eq_dec` per code, literal bytes and no arithmetic) reads back every code by
`refl` (`short_cc_complete`). The fused test after CMP
(`JumpIf(AE, d)` falls through exactly when `l.unsigned_lt_bit(r)`) is one
`cong_fn` from the flags equation. Clients never match on the old
constructors, so keeping the old names as functions leaves them unchanged
(§2.1).

**V4: feasible, with no new lemma kind.** From the code, not a prototype:

- Every region is selected under a contract that its inputs and its
  temporaries are disjoint and its outputs are temporaries
  (`select_here`, structured.rs:88–101; `lower_dag`, 2698). A `Compose`
  places each prefix output in a fresh free temporary (structured.rs:111–118).
  That is the doubling chain's ping-pong between R8 and R9, and it is a
  selector rule, not a proof obligation.
- The certificate derives `_Protected(r)` from the region's clobbered set,
  and the composition proofs ask only for the preservation of values the
  continuation reads (structured_cert.rs:406, 523, 579). Clobbering a dead
  input is therefore already expressible, and a wrong one is refused
  (`false_elim(protected)`).
- Inside a DAG, an input read at a later step is justified by conversion
  seeing through the writes to other registers
  (`placement_at_state`, function_ir_x86_lower.rs:3925). An input overwritten
  at or after its last read keeps every such proof valid, because its last
  read is at the state before the overwriting step.

P is therefore a selector change. `select` gains the set of input registers
the parent does not need afterwards (*consumable*). A `Compose` prefix
output, a `lower_dag` destination (the left operand's register, for a
two-operand `add`/`sub`) and a `Conditional`'s join may take a consumable
input's register at or after its last use. The root's consumable set is
empty unless the caller says otherwise; the field words keep R11, so they
start with one `mov`.

**V5: the arms re-emit their constants.** A constant argument to a helper
(`place(state, threshold, weight)`) is not passed as a port. The reflector
propagates it into the body as a known constant (`known`,
function_ir_source/structured.rs:537), so every region that uses `threshold`
builds its own `Const` node and loads its own `movabs`. F alone does not
remove the second load. **F′**: when a `Conditional`'s prefix loads a
constant that an arm needs again, the arm takes it as an argument port bound
to the prefix's register instead of a `Const` node of its own. The
source-value machinery already carries `SourceValue::Constant` for crossings.
F′ is a region rewrite before selection, lands after F, and is worth about
10 bytes a place (landed as §2.5).

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
