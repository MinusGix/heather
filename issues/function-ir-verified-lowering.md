---
title: Lower FunctionIR's pure regions by a Heather function proved correct once
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-21
updated: 2026-11-09
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

1. **Straight-line dataflow regions.** `lib/native/function_ir/function_ir_lower.hthr`:
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

   *Round 1 as built:* `lib/native/function_ir/function_ir_lower.hthr`, theorem
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

   `lib/native/function_ir/function_ir_lower_structured.hthr` threads round 1's file through
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

   *Round 3 calls as built:* option A of the design question, a `Call`
   node in `StructuredRegion` (Minus, 2026-10-21).
   - `lib/native/function_ir/function_ir.hthr`: `Call(callee, arguments, result)`, at most
     six word arguments. Round 2's `StructuredRegionHolds` says `False` of
     it, so `emit` refuses it and round 2's theorem is unchanged.
     `StructuredRegionHoldsIn(callees, values, region)` reads a call
     through `callees: Callees()`, a relation from a function, its
     arguments and a result. A `Function` is parameters, a body and a
     result id, and `Function::Computes(callees, arguments, result)` is
     that some valuation binds the parameters, satisfies the body and gives
     the result. A program is a list of functions, last first; function `f`
     calls only the ones after it, so a program cannot recurse
     (`program_callees`).
   - `x86_64_stack_runs` gains the spill and reload runs over register
     lists (`List::spills`/`reloads`, `Site::moves_spills`/`moves_reloads`
     against `Stack::Saved`), `moves_branch` with machine-run arms, and
     `returns_weaken`. `moves_call` takes the return address's offset as a
     function of the state.
   - `lib/native/function_ir/function_ir_lower_calls.hthr` lowers with SysV's registers. A
     call spills the eight caller-saved registers other than RAX into the
     caller's frame, moves the arguments into RDI…R9, CALLs `Succ(f)` and
     reloads, so the file after it is the file before it with the result
     in RAX. Body code may not write a callee-saved register (checked by
     evaluation, `leaves_all`), and every callee keeps them by contract.
     Each function is its label, a 64-byte frame, the body
     (`StructuredRegion::emit_calls`, round 2's `emit` with calls), the
     result moved to RAX, the frame freed and RET. Function `k` asks for
     `72 * Succ(k)` bytes of stack below its return address.
   - The contract is `Site::Calls(stack, callees, bound)`. Every function
     below `bound`, entered at its label with its arguments in their
     registers, words its body says may give `result`, and room on the
     stack, returns `result` in RAX. RSP is back, the callee-saved
     registers are kept, and the stack above its return address is
     unchanged. The theorem is `lower_program_correct`: whatever the
     placement, a program `lower_program` returns has every function meet
     it, at any origin and with any stack meeting the `Stack` laws. It is
     proved per function (`Function::emit_returns`, given the earlier
     functions' contracts) and by induction over the list
     (`emit_functions_calls`).
   - The fixture (`fixtures/function_ir_lower_calls_examples.hthr`, checked
     by `function_ir_lower_calls.rs`) lowers `double`, `add_double` (a
     value live across a call) and `pick` (a call in a conditional's arm)
     by `refl`, and instantiates the theorem for one function at its
     offset. Its refusal controls are a value left in RAX across a call
     (the same function lowers when the placement puts it in RCX),
     recursion, a forward call, and seven arguments.
   - Proof-engineering lesson: compose `Moves` stages as separate theorems
     with explicit statements. One theorem composing them inline with lets
     and inferred lambdas cost tens of seconds and millions of conversion
     queries; split into stages, each checks in a fraction of a second. Keep
     `omega` in small lemmas, because inside a large context it slows the
     kernel gate.

   Left for later:
   - A call saves all eight caller-saved registers, live or not, and a
     value may never sit in a callee-saved register, because functions
     have no prologue saves. Saving only the live registers, and letting a
     function save the callee-saved ones it uses, are selection rules with
     their own cases.
   - The stack bound is by function index (`72` bytes a level), not by
     call depth, and a CALL does not keep SysV's 16-byte alignment. That
     only matters when calling foreign code.
   - Word arguments and results only, at most six arguments, and no
     recursion. Loops are [[function-ir-lowering-loops]].
   - The placement planner has no `Call` arm, and nothing plans a whole
     program, so the fixture's placements are written by hand.
   - elf64's process stack meets the `Stack` laws only once the process
     theorem is rebuilt on these runs. The toy memory is the one instance.
   - `x86_64_step_forms`' decoder does not know the stack forms, so
     `MachineStep` has no determinism theorem
     (`linux_x86_64_determinism`'s counterpart).
4. **The CLI through the compiler**: `compile-x86` evaluates `lower` and
   instantiates the theorem instead of generating a certificate per
   function; the immediate forms (`AddRI8`/`AddRI32`, CMP-and-Jcc without a
   materialised bit) come back as selection rules with their own cases in
   the theorem. Then B2 can start.

   *Round 4 as built:* `compile-x86` compiles a word function and the
   functions it calls through `lower_program` (Minus, 2026-10-23: the CLI
   and the planner's calls first; the selection rules are
   [[function-ir-verified-selection-rules]]).
   - **Source to IR by `refl`.** The Rust reflector
     (`crates/elab/src/function_ir_source/program.rs`, untrusted) turns the
     source function and its callees into a program, last function first.
     The certificate states `program_eval(program, f, [a0, a1]) =
     source(a0, a1)` over open words and proves it by `refl`, calls
     included. Two evaluator changes make that convert: `word_value` at
     width 64 is the word itself (transport along `Nat::equation`, a data
     decision, where `eq_dec`'s proof would not unfold), and a
     `Conditional` evaluates by branching at each read of its bit, since
     the kernel has no commuting conversion from an application into a
     match. No per-function source-to-IR theorem is generated.
   - **The planner places calls.** `Function::plan` plans a body without
     calls toward RAX from the scratch pool, and one with calls from
     `call_pool()` (no RAX, which a call's result lands in), with a call's
     result held in RAX in the planner's file. `plan_program` plans every
     function. A call's argument moves are scheduled (`File::call_moves`):
     a move waits while its target holds a source another move still
     needs, and a cycle goes through a free staging register. The
     emitter still checks the outputs, so a bad schedule is a refusal.
   - **The theorem.** `function_ir_compile`'s `compiled_returns`:
     lowered, evaluable, and evaluating to `answer` gives function `f`'s
     returns claim with `answer` in RAX, from `lower_program_correct` and
     `program_eval_computes`.
   - **The certificate** (`crates/cli/src/native/verified.rs`). Each
     statement is its own declaration with its own fuel, and the lowering
     is most of what one spends, so it is evaluated once: the compiler
     reads the code back (`Prog::numbers`, untrusted) and states it as a
     literal, `lower_program(p, plan_program(p)) = Some(code)` by `refl`
     checks it, and everything after evaluates the literal. The bytes go
     a piece of about 256 at a time (`asm_code_after` by `refl`, glued by
     `asm_code_back`): checking a byte has a large constant cost, so one
     equation over a whole program's bytes runs out. Then the
     entry offset, and `{p}_returns` instantiating `compiled_returns`.
   - **The CLI.** Ordinary `compile-x86` tries this first. A source outside
     the reflected fragment (a `Bool` helper, `||`, a loop) still takes the
     per-function certificate, with a note on stderr; a program in the
     fragment that the lowering refuses is an error, never a fallback. The
     assembly is the whole program, each function's frame and RET in it,
     the symbol at the function's label. `build-x86` and the `--callee`
     path are unchanged.
   - Tests: `fixtures/function_ir_compile_examples.hthr`
     (`function_ir_compile.rs`: a value live across calls, swapped and
     rotated arguments, calls in a branch's arms, three levels; controls: a
     wrong source and a rotation without its staging move are refused) and
     `crates/cli/tests/native_program.rs`, which links
     `examples/x86-native/program.hthr` and `sharing.hthr` against C and
     runs them. `native.rs` and `native_branches.rs` now check the verified
     certificate.

   Left for later:
   - The selection rules: [[function-ir-verified-selection-rules]] (done
     2026-10-24; placement entries are `Place`, and the file knows constants
     and comparisons).
   - `lowers` is one declaration over the whole program's lowering;
     larger programs need it per function
     ([[function-ir-verified-compile-cost]]).
   - Loops: neither the reflector nor the planner has them
     ([[function-ir-verified-loop-planning]]).
   - `Bool` helpers and connectives in the reflector, and `build-x86`
     through this path; the old generators retire with B2.

   *B2's first step, as built (2026-10-24):* the reflector takes `||`,
   `&&`, `!`, `Bool` literals, a `match` whose arms are tests, and calls of
   `Bool` helpers of words (inlined, their parameters bound to the
   argument ports). Each becomes a tree of `Conditional`s on plain
   comparisons that tests an operand only where its connective needs it.
   Agreement can't be `refl` there: the source matches on `a || b`, and
   no conversion commutes that with nested conditionals. So the reflector
   also spells the tree in source operations, an *expansion*. The
   certificate proves `program_eval = expansion` by `refl` and
   `expansion = source` by `split_all; all_goals { refl }`. A call of such
   a function is refused ([[function-ir-verified-decided-callees]]).
   `branches.hthr`'s `composed` and the new `either` take this route.
   `native_structured_composition.rs` is gone, and `native_branches.rs`
   now runs both against C, with a refusal control.
5. **The bounded loop** (`docs/native-effect-source-design.md` §5.4, L3):
   FunctionIR's loop of at most `bound` passes with an explicit `Exhausted`
   outcome, lowered and proved inside `emit_calls`.

   *Round 5 as built:* `StructuredRegion::Loop(inputs, bound, parameters,
   count, body, exit, next, outputs, exhausted)` in `lib/native/function_ir/function_ir.hthr`.
   - Its meaning is `LoopRuns`. Each pass binds the state to `parameters`
     and the passes left, counted down from `bound`, to `count`, in a
     valuation of its own, and runs `body`. The bit `exit` set ends the loop
     with the words `next`; otherwise `next` is the next pass's state. With
     no passes left the final state is the current one and `exhausted` is
     set. The evaluator (`function_ir_eval`) runs it by recursion on the
     bound, so FunctionIR stays total.
   - The code is the entry moves into the state registers and the count
     into a counter register, then the head `TEST counter; JE X`, the body,
     `TEST exit; JE C`, the leave moves with the flag cleared and `JMP J`,
     then at `C` the back moves, `ADD counter, -1` (imm8) and `JMP` to the
     head, at `X` the flag set, and `J`. The four labels are the next four
     names; the body's start after them.
   - The loop is a barrier for the register file: after it, the file holds
     the outputs and the exhausted bit and nothing else. The state,
     counter and flag registers must be pairwise apart and caller-saved
     (`LoopRegisters::Apart`, checked by evaluation); anything else is a
     refusal.
   - The proof (`loop_emits`) is an induction over the passes left
     (`Site::loop_passes`) built from separate segment theorems
     (`loop_stops`, `loop_enters`, `loop_body_runs`, `loop_leaves`,
     `loop_rounds`, `loop_marks`), with the counter represented as
     `ofNat(r)`, `r < 2^64`, and decremented by `BitVec::toNat_decrement`.
     The x86 side gained `Site::moves_block`, `moves_jump` (ahead or
     behind) and `moves_test`.
   - A JMP may now land behind it, as a CALL already could. A name no
     label has resolves to offset 0, which a backward jump reaches, so
     `Prog::laid_out` gained `targets_named`: every Jcc, JMP and CALL
     target must be a name of the program (round 2's missing-label control
     caught this).
   - **Well-founded functions:** `loop_runs_unexhausted` takes an
     invariant on the state and a measure that every pass which goes round
     decreases, and shows that a loop entered with the measure below the
     passes left never sets `exhausted`. The pass that leaves is a pass
     too, so the bound is the measure at entry plus one in general, or the
     measure itself when it is positive at every pass (a countdown whose
     measure is `x - 1` takes `bound := x`). This sharpens the design's
     "`bound :=` the measure".
   - The fixture (`fixtures/function_ir_lower_loops_examples.hthr`, checked
     by `function_ir_lower_loops.rs`) evaluates and lowers `triangle` (a
     fold, exhausted by design), `gcd` by subtraction (a conditional in the
     body, bound `a + b`) and `scale` (a call to `double` inside the loop),
     pins each program and instantiates `lower_program_correct`. `twice`
     is a Wf-style countdown proved never exhausted through
     `loop_runs_unexhausted`. Refusals: the flag or counter placed on a
     state register, a body clobbering the counter, a short placement, and
     the flag in a callee-saved register. The Rust side mutates the back
     edge and the exhausted claim, and the kernel refuses both.

   Left for later:
   - A one-bit `Const` is not lowered (`word_only`), so a loop whose exit
     is never set spells its bit as a comparison (`count < count`).
   - The counter is a 64-bit word, so `bound` is read mod `2^64`.
   - Loop state is words only, and the barrier drops every value the loop
     does not output, so a value live across a loop must go through it.
   - Nothing plans a loop's registers; the fixture's placements are by
     hand, like round 3's.
   - The old per-function loop path (`function_ir_loop`) is untouched;
     moving its examples onto this route is part of B2.

## Log

- 2026-11-05: gardener: cites a file it shares with [[function-ir-multi-word-calls]] (`lib/native/function_ir/function_ir.hthr`); [[function-ir-x86-shift-legalization]] (`lib/native/function_ir/function_ir_lower.hthr`).
- 2026-11-09: 2026-11-09: passes composing by simulation-diagram composition, and the four machine closure kits made one, are filed as [[transition-systems-and-simulations]] (docs/native-mathematics-survey.md §3).
- 2026-11-09: `lower_nodes` is also a star diagram from leaves to x86 code, composed after the pass (`compile_star`, `List::compiled_runs` in function_ir_lower_diagrams.hthr): [[s4-lowering-as-diagram]].
