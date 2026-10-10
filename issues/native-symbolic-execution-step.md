---
title: A symbolic-execution step that emits a placed instruction run's proof
status: closed
labels: [native,x86,tactics,proofs]
created: 2026-10-07
updated: 2026-10-10
---

With [[native-straight-code-triples]] in place, the remaining per-instruction
work is mechanical: given the placed pieces, a state with its `memory_is` and
`rip_is`, run one block, byte or word load, store or near jump, and produce
the next state with its facts. Today that is three to six `let`s per
instruction group (`elf64_command.hthr:2210-2240` is typical), and a
conditional jump also needs its flag fact proved by hand
(`trans(cong_fn<…>(λ v => is_zero_bits(64, v.sub(word_zero())), …), …)`).

Wanted: a `meta fn` (or elaborator sugar) that emits those ordinary terms:
one call per straight run, deciding a `Jcc` from the flags by `decide` or
`bv_omega` when it can, and leaving the branch as a goal when it cannot.
The kernel still checks every emitted term; nothing is trusted.

## What it assumes from elsewhere

- **[[native-straight-code-triples]]** owns the triple types the step
  composes into. Assumed here: only that a step's result is one of them.
- **[[tactic-composition-ergonomics]]** owns how such a step composes with
  other tactics.

## Log

- 2026-10-10: **Landed in-language, not as a `meta fn`: a computed obligation and one theorem** (`lib/elf64_straight.hthr`, `docs/native-straight-runs-design.md`). Closes the issue.

    - `Straight(file, page, origin, goal, labels, l, n)(vars, state)` reads the `n` items ending at label `l` and states what running them comes to: a block's, load's or store's state is the item's own result, a store sets its slot in `vars`, a JCC is a pair of implications on its condition (the side a precondition rules out is `absurd`; the other is the branch left as a goal), a taken JCC or JMP ends at a leaf. `straight_runs` proves `goal(state)` from it for any `goal` with `StepsBack`; `cmd_straight` is it for the command's program.
    - `x86_64_asm` has `Load(WordLoad)` and `Store(WordStore)` items so the computation can read them; wc's bytes are unchanged (same sha256 as master).
    - Moved: `loop_last`, `operand_head`, `stdin_path`, `open_back`, `failed_runs` (see [[native-runs-remaining]]).
    - Lesson: keep the computed type structural. Reading a slot address (`slot_find`) or a label (`asm_find`) inside the type runs the elaborator's evaluation, which ran out of fuel or dominated; the caller names the slot and the label and proves them by `refl`. Landings are cited in the stretch's own spelling (`cmd_lands`).

    Cost, cold, against master: the five phases take slightly fewer kernel steps than the chains and helpers they replace; the runner and `asm_code_back` are paid once, so the module's total steps rise by well under a percent. Elaboration rose: the elaborator unfolds `Straight` by substitution at every nested constructor, now most of each moved phase's time and a noticeable share of the module's wall time. Filed as [[elab-whnf-copies-straight-continuations]].
