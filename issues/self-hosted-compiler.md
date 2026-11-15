---
title: Compile the native compiler natively and run it in write-elf's place
status: open
labels: [native,self-hosting,performance]
area: heather-in-heather
milestone: [self-compiler]
created: 2026-10-31
updated: 2026-10-31
---

Round R11 of `docs/native/compiler-milestones-proposal.md` (§5, §7), milestone `self-compiler`: the native compiler,
compiled natively. This is the second half of what
[[self-hosting-first-component]] filed.

## Scope

- Compile `Source::compile`, the allocation check and the encoder (all Heather, `lib/native/native_compile*.hthr`, `native_alloc.hthr`) as `runtime fn`s.
- `write-elf` runs that binary where it now evaluates the compile on its fork (`evaluate_numbers`, `crates/cli/src/native/elf.rs`). The kernel's check of the emission is unchanged, so a bug is a refusal and not a wrong certificate.

## Done when

`write-elf` builds the regression corpus through it, and `scripts/perf ab` shows the fork's read-back counters gone.

## What it assumes from elsewhere

- **[[native-compiled-procedures]]** and **[[native-heap-arena]]**: the compiler is code with procedures and lists.

## Log

- 2026-11-05: gardener: cites a file it shares with [[kernel-failed-conversion-cost]] (`crates/cli/src/native/elf.rs`); [[native-procedures-write-elf-capacity]] (`crates/cli/src/native/elf.rs`).
