---
title: A store of no bytes changes nothing and needs no room, at every address
status: closed
labels: [stdlib,x86,memory,proofs]
area: heather-in-heather
milestone: [hih-memory-model]
created: 2026-11-26
updated: 2026-11-26
---

The bytes-level language accepts a read of zero bytes into a window that
starts exactly at its block's end, as an empty slice at a list's end is
fine. On the machine, the Linux model asks that the buffer be writable for
zero bytes and stores an empty list there. `ByteWrites`
(`lib/std/arch/x86_64/x86_64_store.hthr`) has no laws; the laws about
writes are the `Stack`'s and the `Loan`'s, and every `Loan` law needs an
offset strictly inside its span (`k < spans.size(b)`). So nothing gives
"writable for zero bytes" or "a store of no bytes leaves memory as it was",
and the lowering of system calls carries it as a hypothesis (at each span's
end address, `writable(m, a, 0)` and `store(m, a, Nil) = m` for every `m`).

(The coordinating session filed this on `claude/bytes-level-lowering-world`;
the file was not on that branch when this round started, so it is restated
here from the round's brief.)

## The law (decided)

A store of no bytes changes nothing and needs no room, and an empty range
is always writable: at every address, not only at span ends. It is a fact
about memory, not about Linux and not about lending. The Linux model and the
language do not change.

## Acceptance

- The law stated once, as a proposition of a `ByteWrites`, and proved for
  each instance in the library (`X86Profile::writes`, `linux_writes`).
- Carried by one record so that the holder of a `Loan` derives it at every
  address with no premise, and every construction of `Stack`/`Loan`
  supplies it from the instance's proof.
- Empty-range lemmas in the memory contract beside the `Loan` laws (whose
  statements do not loosen): writable, keeps memory, keeps code, keeps the
  stack words, keeps `Injected`.
- A probe in the memory contract's tests: from a `Loan`, for every memory
  `m` and address `a`, `writable(m, a, 0)` and `store(m, a, Nil) = m`.
- No generated certificate changes (`scripts/linked --check`).

## Log

- 2026-11-26: landed (d90fb2b). The law is `ByteWrites::EmptyRange`
  (x86_64_store): `writable(m, a, 0) ∧ store(m, a, []) = m` for every `m`,
  `a`. **`Stack` carries it** (`Stack.empty`), not `Loan`: it is a law of
  `writes`, which the stack owns, and the generic `Stack::loan_none` could
  not cite an instance proof for a `Loan` field; on `Stack` the one
  constructor (`DataRegion::stack`) cites `X86Profile::writes_empty`, and
  no `Loan` construction (`DataRegion::loan`, `Target::loan`, `loan_none`,
  `Loan::sub`) changes. Instances: `X86Profile::writes` (`writable_none`:
  `Allows` below zero is vacuous; `store_none`: `refl`, the empty
  `put_from` is the cells and record η gives the memory); `linux_writes` is
  no instance by itself (`LinuxIo` states no laws) — `linux_writes_empty`
  transports the law to an io built from lawful writes, and
  `X86Profile::linux_empty` is the profile's. Contract lemmas:
  `Loan::empty_writable`, `empty_store`, `empty_reads`, `empty_keeps`,
  `empty_keeps_code`, `empty_injected` (memory side; the heap is unchanged).
  Probes: `loan_empty_range` (the lowering's hypothesis from a `Loan`),
  `pair_end_empty` (one past the written span), control
  `counting_not_empty`. `Spans::Window` lives in x86_64_call_contract,
  outside this round. The one surprise: the elab fixture's toy store
  (x86_64_stack_runs_examples) kept the law only pointwise (no funext), so
  `toy_store` now returns the memory on `[]`. `scripts/linked --check`
  unchanged; `HEATHER_PR_NATIVE=all scripts/test --pr`:
  `== suite: 4140 passed, 0 failed, 3 ignored ==`.
- 2026-11-26: First filed by the bytes-level-lowering-world session on its own branch (the smallest program and the survey of instances); this file is the building session's, kept at the merge.
