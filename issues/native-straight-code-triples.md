---
title: Triples and frame sets for straight native code, proved once
status: open
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
