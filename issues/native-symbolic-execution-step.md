---
title: A symbolic-execution step that emits a placed instruction run's proof
status: open
labels: [native,x86,tactics,proofs]
created: 2026-10-07
updated: 2026-10-07
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
