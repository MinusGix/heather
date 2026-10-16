# Straight native code as triples: `Runs`

Issue: `issues/native-straight-code-triples.md`. Library: `lib/elf64_runs.hthr`;
client: the phases of `lib/elf64_command.hthr` listed under "Moved" below.

## The judgment

```heather
fn Runs(pre: MachineState<IoMemory> → Type, from: BitVec(64),
        post: MachineState<IoMemory> → Type, to: BitVec(64)) → Type {
    (state) → state.rip = from → pre(state) →
        Exists(λ after => LinuxSteps(io_linux(), state, after) ∧ ((after.rip = to) ∧ post(after)))
}
```

From any state at `from` that satisfies `pre`, Linux steps reach a state at
`to` that satisfies `post`. `pre` and `post` are predicates on one state.
A fact that relates the end to the start, such as "slot 19 now holds what RBX
held", is stated over a ghost value the caller binds as a theorem parameter
(`c19`). The precondition says `read_gpr(Rbx, s.gprs) = c19`, and the
postcondition names `c19`. That keeps sequencing plain composition, and
nothing in a postcondition is an existential over the earlier state.

## Rules (proved once)

| Rule | What it takes |
| --- | --- |
| `runs_seq` | `Runs(p, a, q, b)`, `Runs(q, b, r, c)` |
| `runs_pre` / `runs_post` | an implication on states |
| `runs_here` | nothing: no step |
| `runs_steps` | a step proved any other way |
| `runs_block` | residency under `pre`, and `post` of `execute_block_normal(instructions, s)` given `pre(s)` and the block's unchanged memory |
| `runs_jcc_passed` / `runs_jcc_taken` / `runs_jcc_taken_back` | residency, the flag's value under `pre`, and `post` of the jump's state |
| `runs_branch` | both sides as `Runs` to one end, and `stays` (the precondition over the jump) |
| `runs_jmp` / `runs_jmp_back` | a JMP and its landing fact |
| `runs_into` | a `Runs` followed by a `LinuxRuns` continuation, which gives a `LinuxRuns` |
| `runs_elim` | a `Runs` followed by any goal, given the end state bound |

A block's postcondition obligation is stated on the block's own result. The
kernel computes `read_gpr(r, execute_block_normal(…, s).gprs)` down to `s`'s
registers for any register the block does not write. So "RSI is kept" and
"R11 holds slot 23's address" are `refl` and `held.right`, not a lemma per
instruction. That is the symbolic-execution step
(`issues/native-symbolic-execution-step.md`) done by conversion, one block at
a time.

`Keeps(regs, after, before)` and `SlotsKeep(slots, after, before)` are the frame
conditions over a register list and a slot list. Each has refl and trans by list
induction, and `slots_keep_apart` takes a slot list that avoids the changed slot,
decided by evaluation. The process libraries' own records (`FmtKept`,
`WriteKept`, `CursorKept`) are not yet restated over them.

## The command's frame: `Framed`

```heather
fn Framed(file, page, vars) → MachineState<IoMemory> → Type {
    λ s => Exists(λ frame => (s.memory = IoMemory(with_frame(file, frame), page)) ∧ FrameHolds(frame, vars))
}
```

The command's state between phases is a function from slots to words
(`vars`), updated slot by slot with `set_var`. `Framed` hides which frame
holds it. `runs_slot_store`, `runs_slot_load` and `runs_frame_store` are the
command's frame-aware rules. A store's postcondition obligation receives
`Framed(file, page, set_var(vars, q, w))` of the state after it. Residency
comes from `framed_resident`: the command's code is placed in every frame's
image (`CommandPlaced`), so it is resident in a framed state.

`runs_slot_test` is the load of a slot into RAX and its compare with zero,
the command's usual test before a `Jcc`. A system call is not a rule: a run
ends at the `syscall`, and `runs_into` hands its end to the library's
`linux_runs_*` lemma for that call (`closes_runs`).

A phase is then a `runs_seq` chain whose middle predicates are written out
(`p0`…`p3` in `stdin_path`, `open_back`). A predicate that needs a register
read at the phase's start names it as a ghost value (`c19`, `mask`) or as
the start's registers (`g` in `SpillPre`, which keeps the state registers by
`WriteKept`).

## Consuming a run

The theorem that consumes a phase calls `runs_into` (when a `LinuxRuns`
follows) or `runs_elim` (for any other goal). Both hand the end state to a
λ as a bound variable. Never project it out of a `let`-bound run
(`ran.witness`, `ran.proof`): the end state is then a projection of the
run's proof term, and every later conversion that meets it unfolds the
whole proof to reach the state. Projecting this way once made `spill_row`
ten times dearer than the hand-threaded proof it replaced; binding the end
state made it ten times cheaper instead. Inside a continuation, `h.witness`
of a bound `h: Framed(…)(s)` is cheap for the same reason.

A frame is bound the same way. A phase whose continuation needs the frame
it started with (a closure over `frame` and `holds`, as in `named_runs`)
cannot take it from `Framed`, whose witness is a fresh frame; such a phase
stays hand-threaded until its continuation takes `Framed` itself.

## Why it is cheaper

The hand-threaded proofs named each intermediate frame concretely
(`stored_frame(file, stored_frame(file, frame, 19, w19), 20, w20)`). The
kernel then met those terms against the placement facts for every later
piece. Under `Framed` the frame is a bound witness. A piece's residency is
checked once inside `framed_resident`, against an abstract frame. Each moved
phase takes several times fewer kernel steps, the spill and the close an
order of magnitude fewer, and the command module as a whole about a third of
what it took hand-threaded. The rules themselves are paid once.
`runs_frame_store` is the dearest because of its `omega` bound.

## Moved

The loop's head and cursor store (`operand_head`, `cursor_store_runs`,
`last_tested_runs`, `loop_last`), stdin (`stdin_path`), the open's return
(`open_back`), the read pass's spill and row setup (`spill_one_runs`,
`spill_runs`, `spill_row`), the prologue's keep and begin phases
(`keep_runs`, `keep_single`, `begin_store_runs`, `begin_test`), the close
(`closes_runs`), the failed path (`failed_runs`) and the total row
(`total_runs`, `total_rows`). The spill block is an `x86_64_asm` program
(`lsp_*`), so the command has no `layout_code` left.

Since moved again, onto one computed stretch each
(`docs/native-straight-runs-design.md`): the loop's last-operand test
(`loop_last`, absorbing `cursor_store_runs` and `last_tested_runs`),
`operand_head`, `stdin_path`, `open_back` and `failed_runs`; then, with a
byte-load item, the dash and ahead tests (`dash_test`, `dash_ahead`) and
`open_path`; then, once their continuations took a frame (`FramedWrite`,
`CursorGoes`), the name's scan and write (`name_scan`, `name_send`), the
read's failure (`read_failed`) and the loop's cursor (`loop_cursor`); then,
with a byte-store item and the page carried through a stretch, the row's
tail (`named_runs`, `unnamed_runs`, `newline_send`), and `init_runs` as a
stretch per slot (`zero_runs`).

## Not yet moved
- `inputs_runs` only composes other phases. `total_runs`, the prologue and
  the spill are still `Runs` chains.
- The other process libraries (formatter, scan, cursor, stat pass, row), and
  their own frame records (`FmtKept`, `WriteKept`, `CursorKept`) over
  `Keeps`.
- The list layouts in `elf64_read_pieces`, `elf64_read_filter` and
  `elf64_count_print`.
