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

   *Round 1 as built:* `lib/function_ir_lower.hthr`, theorem
   `Region::lower_correct` (with `execute_block_memory`,
   `execute_block_rip` and `execute_block_kept` for the frame). The
   examples and refusal controls are
   `crates/elab/tests/fixtures/function_ir_lower_examples.hthr`, checked by
   `crates/elab/tests/function_ir_lower.rs`; each region's claim is the
   theorem applied to a `refl` fact about `Region::lower_planned`, and the code
   matches what the Rust lowering emits for `add64`. Proof idiom: every
   function that branches on a computed value takes it as a parameter (a
   `Found`, an `Option<Lowered>`, a decision), so each proof matches on a
   variable; the list and region proofs (`lower_nodes`, `File::move_outputs`,
   `Region::lower`), which cannot, match with an explicit `as` motive
   applied to the step's lemma.
   The theorem needs no `RegionValid`: validity only makes the valuation
   it quantifies over exist.

   Left for later rounds, all selection rules with their own theorem
   cases: a `Move` whose source is already in its destination still emits
   `MOV r, r`; `OP d, b` into the right operand's register for commutative
   ops (today that placement is refused); the immediate forms; one-bit
   constants and copies. The frame lemmas are about any instruction list
   and may belong in `x86_64_block`. `read_gpr`/`write_gpr` as `Gprs`
   methods is [[gprs-read-write-methods]].
2. **Conditionals** (`StructuredRegion`'s `Conditional`, `Sequence`,
   `Compose`): code as a `Prog` with `Jcc`/`Jmp` to labels, proved over
   the assembled bytes. This is where S2's `Wp` (its `Jcc`/`Jmp`
   obligations) would be the natural tool; if S2 is not there yet, the
   round proves the pure, syscall-free fragment of it it needs and S2
   generalises it. `branches.hthr` through it.

   *Round 2 as built:* S2 was not there, so the round proved the pure
   fragment itself, in the foundation:
   `lib/std/arch/x86_64/x86_64_asm_runs.hthr`. `Site::Runs(from, to, pre,
   post)` says that from offset `from` of a label program resident at
   `origin`, registers satisfying `pre` run fetched to offset `to`, with
   registers satisfying `post` and memory untouched. It has one lemma per
   emitted form, each over any program: `runs_block`, `runs_jump`, and
   `runs_branch` (`TEST r, r; JE else; yes; JMP join; else: no; join:`),
   plus `runs_trans`/`runs_weaken`/`runs_frame`. No lemma does arithmetic
   on open offsets. The producer checks the finished program once by
   evaluation (`Prog::laid_out`: no holes, unique names, every jump landing
   on its label by `asm_lands`), and `label_target`, `jcc_lands` and
   `jmp_lands` read the landings off that check.

   `lib/function_ir_lower_structured.hthr` threads round 1's file through
   `StructuredRegion::emit`:
   - a dataflow leaf is one `Block`;
   - a `Conditional` finds its condition as a `Bit` in a register and lowers
     both arms from the same file;
   - the join's file is `File::meet`, what both arms agree on. Arms that
     leave an output apart make the final move fail, so `lower` refuses.

   The theorem is `StructuredRegion::lower_correct`, over every placement.
   For any origin, fetch and data access, and any bytes `last` after the
   program, a program `lower` returns, resident, runs fetched from its
   start to its end and leaves the outputs in their registers. The examples
   (`fixtures/function_ir_lower_structured_examples.hthr`, checked by
   `function_ir_lower_structured.rs`) are branches.hthr's shapes: `select`,
   `nested_true`, `keep_below` (an arm returning an input) and `composed` (a
   conditional on a conditional's bit). Each program is computed by `refl`.
   The refusal controls are: arms apart, a word condition, a clobbered
   condition, and two programs `laid_out` rejects.

   Left for later rounds:
   - A conditional on a comparison materialises the bit (`XOR; CMP; SETcc;
     TEST; JE`). CMP and Jcc on its flags is round 4's selection rule.
   - `Runs` speaks of registers only. The callee-saved frame across a
     branch (`Kept`, round 1's `execute_block_kept`) is not in its `post`
     yet, and round 3 needs it.
   - `laid_out`'s landing check walks the program once per jump.
   - The examples are StructuredRegions written by hand in the shapes the
     structured source generator produces. The generator's output goes
     through `lower` in round 4.
   - `Site::Runs` is S2's `Wp` restricted to pure code; [[native-one-wp]]
     generalises it to states and syscalls.
3. **Calls and the stack** (`calls`, `composition`, `sharing`,
   `stack_local`, `stack_save`, …): a callee's contract as a `Proved`-shaped
   item, the frame view, spills.

   *Round 3 foundation as built:* `x86_64_calls` and its friends burn in
   B2, so the stack is new foundation, not salvage.
   - `lib/std/arch/x86_64/x86_64_stack.hthr` has four step forms: a word
     spilled to and reloaded from `[rsp + disp8]`, CALL rel32 and RET. A
     `MachineStep` is a fetched step, a store, or one of them. A process
     gives its program a `Stack`: `size` bytes from `low`, writable,
     canonical, word reads seeing exactly the stores made into them, and
     code untouched by those stores. These are a profile's laws, proved
     once for its memory. Proofs name stack addresses by offset from `low`
     (`push_at`, `pop_at`, `slot_at`), so none does arithmetic on an open
     address. `BitVec::sign_extend_clear_toNat` is what lets a small
     displacement read as itself.
   - `x86_64_asm` gains `CallTo(target)`, `Ret`, `Spill` and `Reload`
     items. `Prog::laid_out` checks that a call lands on its label, ahead or
     behind (`call_lands`).
   - Round 1's frame lemmas (`Kept`, `leaves`, `execute_block_kept`,
     `callee_saved`) moved down to `x86_64_kept` so the foundation can
     state them.
   - `lib/std/arch/x86_64/x86_64_stack_runs.hthr` has `Site::Moves`, the
     state-level `Runs`. Conditions are over whole states, the program
     stays resident, and a frame is stated against a ghost state.
     `moves_of_runs` lifts round 2's pure runs, so round 2 is unchanged. The
     stack forms' lemmas are `moves_spill`, `moves_reload` and
     `moves_call`. A callee's contract is `Site::Returns`: entered at stack
     offset `i` with the return address there, it returns there with RSP
     at `i + 8` and `post(i, entry, exit)`. `returns_by` closes a body by
     RET into one.
   - The fixture (`fixtures/x86_64_stack_runs_examples.hthr`, checked by
     `x86_64_stack_runs.rs`) proves a two-instruction callee's contract and
     composes a caller's CALL against it by hand. A toy memory (code a map
     of its own, one byte per address value) meets the `Stack` laws, so they
     are satisfiable, and the caller's theorem is instantiated at it.

   Left for the rest of the round: calls in FunctionIR and their lowering
   (the frame across a branch, `Kept` in the theorem, a `moves_branch` with
   machine-run arms), and spills. Left for later:
   - elf64's process stack meets the `Stack` laws only once the process
     theorem is rebuilt on these runs; the toy memory is the one instance.
   - `x86_64_step_forms`' decoder does not know the stack forms, so
     `MachineStep` has no determinism theorem
     (`linux_x86_64_determinism`'s counterpart).
4. **The CLI through the compiler**: `compile-x86` evaluates `lower` and
   instantiates the theorem instead of generating a certificate per
   function; the immediate forms (`AddRI8`/`AddRI32`, CMP-and-Jcc without a
   materialised bit) come back as selection rules with their own cases in
   the theorem. Then B2 can start.
