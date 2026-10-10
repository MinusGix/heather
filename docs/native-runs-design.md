# Straight native code as triples: `Runs`

Issue: `issues/native-straight-code-triples.md`. Library: `lib/elf64_runs.hthr`;
first client: the operand loop of `lib/elf64_command.hthr`.

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
| `runs_jcc_passed` / `runs_jcc_taken` | residency, the flag's value under `pre`, and `post` of the jump's state |
| `runs_branch` | both sides as `Runs` to one end, and `stays` (the precondition over the jump) |
| `runs_jmp` | a forward JMP and its landing fact |
| `runs_into` | a `Runs` followed by a `LinuxRuns` continuation, which gives a `LinuxRuns` |

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

A phase is then a `runs_seq` chain whose middle predicates are written out
(`p0`…`p3` in `stdin_path`, `open_back`). The theorem that consumes the phase
calls `runs_into`, or reads the end state out of the `Runs` with `.witness`
and `.proof`.

## Why it is cheaper

The hand-threaded proofs named each intermediate frame concretely
(`stored_frame(file, stored_frame(file, frame, 19, w19), 20, w20)`). The
kernel then met those terms against the placement facts for every later
piece. Under `Framed` the frame is a bound witness. A piece's residency is
checked once inside `framed_resident`, against an abstract frame. The phases
moved so far (the loop head, the stdin path and both branches of the open's
return) take several times fewer kernel steps each. `cursor_store` and
`stdin_path` take about an order of magnitude fewer. The rules themselves are
paid once. `runs_frame_store` is the dearest because of its `omega` bound.

## Not yet moved

- The dash and ahead tests (`ByteTested`, `jne_open`, `dash_second`,
  `dash_test`) and `open_path` (a syscall: it needs a `runs_*` rule over
  `linux_runs_open`, or stays CPS).
- The read pass's spill and row (`spill_one`, `spill_run`, `spill_row`). These
  are the costliest items in the module, and the spill block still lists its
  own lengths (`spill_lens`).
- The other process libraries (formatter, scan, cursor, stat pass, row).
