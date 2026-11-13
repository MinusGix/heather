---
title: A loop's lowering hands on the words it used
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-12
updated: 2026-11-12
---

`ELoop::lower` (`lib/native/runtime/rt_io_loop.hthr`) lowers a `While`'s
condition, body and rest each from the same `next`, and hands on the
rest's `next`. The condition and body use words past it, so a `Source`
sized by the lowering's `next` has too few words: `write-elf` refused
`tr_lend_source` with "word 6 is past the 6 word slots" until the test
sized it by `Stmt::word_bound`. Sound as it stands, since `next` means
"free from here on" only for what follows, but a `runtime fn main` that
publishes the lowered `Source` needs the high-water mark.

## Scope

- Either the publisher sizes the file by `stmt.word_bound()` (what the
  test does), or `ELowered` carries a bound the lowering proves covers
  every word its statement names. The first is a line; the second lets a
  theorem state the file is wide enough.

## Done when

The step that turns a lowered computation into a `Source` sizes the file
so that every lowered program's words fit, with a probe of a loop.
