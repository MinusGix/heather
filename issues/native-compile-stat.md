---
title: Compile stat in the effectful source's compiler
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-source]
created: 2026-10-28
updated: 2026-10-28
---

`Prog::call` (`lib/native/native_compile.hthr`) compiles reads, writes,
`open` and `close`; `StatsPath` and `StatsFd` are still refused (reason 7).
Split from [[native-compile-other-calls]] when round 7 of
`docs/native/native-real-programs-plan.md` landed open/close: no `hih-tools` tool
needs stat, so it carries no milestone of that line.

## Scope

- `StatsPath`: the path copied with its NUL into scratch as `Opens` does
  (`Target::goes_path_loop`, `lib/native/native_compile_opens.hthr`), so the
  stat record cannot land in scratch too; it needs its own range or a copy
  after the path is spent.
- `StatsFd`: operands from word slots, as `goes_closes`.
- Both land a stat record in a buffer. Whether Linux may leave the range
  written on failure decides whether they land in scratch and copy, as a read
  does (`goes_read_back_ok`/`_failed`).
- The first customer is GNU `cat`'s check that an input is not its output,
  or `wc`'s column width (plan §7).

## Log

- 2026-11-05: gardener: cites a file it shares with [[native-compiled-code-shape]] (`lib/native/native_compile.hthr`); [[native-homes-read-in-place]] (`lib/native/native_compile.hthr`).
