---
title: Make the slot allocator's verdict cheap enough to state by refl
status: open
labels: [native,x86,perf]
area: heather-in-heather
created: 2026-10-31
updated: 2026-10-31
---

`refused(tr_upper()) = []` by `refl` runs out of kernel fuel
(`lib/_tests/native/native_structured_tests.hthr`), and so does the same
check over a builder tool whose region loop is followed by `write_all`
(found 2026-10-31 in native_build_tests), while smaller sources pass and
the certificate `write-elf` checks for the same tools passes. Evaluating
the slot allocator's loop-set closure (`Source::loop_sets`, up to
`words * words` passes) over a region loop with more live words is the
likely cost; it moved here from [[native-region-spelling]].

## Scope

- Measure where the fuel goes (`--timings`, `scripts/timings`) and make the
  closure cheap enough for a test to state a mid-sized tool's verdict by
  `refl`, or say why the test should state it another way.
