---
title: Prove that native code erases secrets at a cut (canonical state at boundaries)
status: open
labels: [native, x86, security]
area: heather-in-heather
created: 2026-10-30
updated: 2026-10-30
---

Minus (2026-10-30), after Frank Denis's three zeroization posts: not an
immediate feature, but worth keeping for secure code. The goal is to prove
that at some point an old value no longer exists in any readable memory,
which covers registers, spill slots, frames, copies and the allocator.

Design and survey: `docs/zeroization-survey.md`. In short, erasure is
non-interference at a cut over the whole `MachineState`. The compiler
reduces it to a one-run **canonical state** (everything outside the keep set
is zero) plus a source-level fact about the kept words. So the compiler
wipes everything not live and proves it did, without knowing what is
secret. The compiler theorem becomes `SimProgram` plus `Canonical` at cuts,
and every later pass must preserve both.

## Scope when picked up

The note's §9 is the order: the statement and lemmas first, then a scrub
at exit, then cuts inside the program, then source erasure, then cheaper
scrubs.

## What it assumes from elsewhere

- **[[native-allocator-class]]** / `docs/native-register-allocation-design.md`
  owns homes. Assumed here: only that a word's home is a slot or a pool
  register, and that the pool is known per compile.
- The heap allocator does not exist yet (milestone `hih-memory`). The note
  says how the invariant forces scrub-on-free once it does.

## Log

- 2026-10-30: Minus attached *High-assurance zeroization* (TCHES 2024), which is now read in full, in `docs/zeroization-survey.md` §8.1. Jasmin's machine-checked theorem is one-run: invalid memory is unchanged or zero. The design adopts that keep-or-zero form for `Canonical`. What Heather would add: registers and flags inside the theorem, the non-interference step proved rather than argued, and a source obligation on kept words.
