---
title: Build a dozen GNU-compatible tools natively and test them against GNU
status: open
labels: [native,examples,tests]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
---

Round 10 of `docs/native-real-programs-plan.md` (§2, §6), and the round that
closes `hih-tools`. The plan's tools are built by `write-elf` through the
verified compiler, with no per-program proof, and tested against GNU.

## Scope

- `lib/native/tools/`: `true`, `false`, `cat [FILE…]`, `head -c N`,
  `head -n N [FILE]`, `yes [STR]`, `echo`, `basename`, `dirname`,
  `tr SET1 SET2` (ranges and literals), `rev`, `wc [-clw] [FILE…]`, `cmp`,
  `grep -F PAT [FILE…]`, `sort` (small inputs), and `uniq`, `tac`, `tail -c`,
  `od -c` if they fall out.
- `crates/cli/tests/native_tools.rs`, outside the fast lane: each tool
  against the host's GNU tool under `LC_ALL=C` on fixed and random inputs,
  including failing opens, failing writes (`/dev/full`), and bad flags.
- Where a tool's behaviour is limited (sizes, flags), the limit is written
  in the tool's file and the test pins it.

## Done when

Every tool above passes. Then `hih-tools` is done.

## What it assumes from elsewhere

Rounds 1–9 of the plan: [[native-source-bytes]], [[native-compile-capacity]],
[[native-elf-every-program]], [[native-compile-wider-leaves]],
[[native-source-builder]], [[native-source-argv]],
[[native-compile-other-calls]], [[native-data-capacity]],
[[native-decimal-io]].
