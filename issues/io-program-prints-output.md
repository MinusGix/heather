---
title: A runtime fn main writes its answer to stdout
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-16
updated: 2026-11-16
---

`runtime fn main(mut io: Io, …)` programs (docs/native/io-programs-design.md)
answer only by exit status: `examples/utf8/utf8check.hthr` exits 0, 1 or 2.
Since #691 (`ETm::If`) a program can branch on a write's outcome and exit 1
when it fails, as `tr_upper` does, so a program can also print.

## Scope

- A demo program that prints: the UTF-8 checker reporting the offset of the
  first invalid byte, or a program writing a computed buffer.
- Its native gate checks stdout and the `/dev/full` exit, as tr's does.
- Prerequisite for [[io-program-demo-mains]] (sort writes its buffer back).
  Byte literals (separate thread) make fixed messages cheap to spell.
