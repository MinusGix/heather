---
title: Triples and frame sets for straight native code, proved once
status: closed
labels: [native,x86,proofs,design]
created: 2026-10-07
updated: 2026-10-10
---

Library processes prove straight code by threading machine states by hand
(`elf64_command.hthr:2210`, `loop_last`): `run_block`, `execute_block_normal`,
`run_near`, `jcc_taken`, then `fetched_steps_trans` to compose, with
`memory_is` and `rip_is` passed along each step. Across `lib/elf64_*` there
are 140 `run_block` calls, 228 `fetched_steps_trans` and 183
`execute_block_normal`. Each phase also declares a record that is a
postcondition with an existential after-state (`SlotStored`, `CursorStored`,
`OperandAt`; 13 records in `elf64_command`). C3's log found that splitting
proofs at abstract states described by records cut the module's cold check
to under a quarter: a triple discipline, arrived at by hand.

Frame conditions are spelled register by register and composed through
projection paths (`FmtKept` and `fmt_kept_trans`,
`elf64_format_width.hthr:298`, eight `.right` deep); frame slots likewise
(`Vars`, `slot_vars` re-proving each field with `set_var_other`,
`elf64_command.hthr:752`, `:2130`).

Wanted, as library types with their rules proved once:

- **`Runs<P, Q>(file, from, to)`**: from any state at `from` satisfying `P`,
  Linux steps reach a state at `to` satisfying `Q`. Sequencing, consequence
  and a branch rule (`Jcc` taken or not by a flag fact).
- **`Keeps(regs: List<Gpr>, before, after)`** and
  **`SlotsKeep(slots: List<Nat>, vars, vars')`**, with transitivity and
  weakening by list induction. They replace `FmtKept`, `WriteKept`,
  `StatCarried` and the per-field `slot_vars` proofs.
- `Placed`, `Ran`, `run_block` and `run_near` move out of
  `elf64_format_width` (`:308-350`) into a module of their own; today every
  process imports the formatter to get them.

Acceptance: one phase of `elf64_command` (the operand loop, `:2125-2400`)
rewritten over these, with its cold check no dearer.

## What it assumes from elsewhere

- **[[native-one-program-logic]]** owns the eventual single program logic.
  Assumed here: only that a straight-code triple over Linux steps is a
  special case it can absorb, not a competing design.

## Log

- 2026-10-10: Inherits from [[native-label-assembler]] (closed): the command's spill block (`spill_lens`, `elf64_command.hthr:65`) and the list layouts left in `elf64_read_pieces`, `elf64_read_filter` and `elf64_count_print` (`layout_code`/`layout_at`). They are straight code whose proofs this issue rewrites; move them onto `x86_64_asm` labels with those proofs.
- 2026-10-10: **Landed: `Runs` triples (`lib/elf64_runs.hthr`), the command's frame rules, and most of the command's phases over them.** Closes the issue; the residue is [[native-runs-remaining]].

  - `Runs(pre, from, post, to)` with sequencing, consequence, a no-step rule,
    blocks, forward and backward `Jcc`/`JMP`, a two-sided branch, and two ways
    to consume a run (`runs_into` before a `LinuxRuns`, `runs_elim` before any
    goal). `Placed`, `Ran`, `run_block` and `run_near` moved there from the
    formatter. `Keeps`/`SlotsKeep` have refl, trans and list weakening.
  - The command's state between phases is `Framed(file, page, vars)`: some frame
    holds `vars`. `runs_slot_store`/`_load`, `runs_frame_store`/`_load` and
    `runs_slot_test` are its rules; residency comes once from `framed_resident`.
  - A block's postcondition is proved on `execute_block_normal`'s own result by
    conversion (registers it does not write read back as `refl`), which is the
    per-block form of [[native-symbolic-execution-step]].
  - Moved: the operand loop's head and cursor store (the acceptance phase), stdin,
    the open's return, the spill and row setup, the keep and begin phases, the
    close, the failed path and the total row. The spill block is an `x86_64_asm`
    program, so the command has no layout list left. The record per phase
    (`CursorStored`, `SpillOut`, `KeepStored`, `BeginStored`) is gone.
  - The lesson, in `docs/native-runs-design.md` ("Consuming a run"): bind a run's
    end state in a λ, never project it out of a `let`-bound run; projecting made
    the spill's row ten times dearer than the hand-threaded proof.

  Cost: the command module's cold check takes about a third of the kernel steps
  it took before (the whole check of it with its imports, about seven tenths).
  Every moved phase is several times cheaper, the spill and the close an order
  of magnitude.
