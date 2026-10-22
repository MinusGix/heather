---
title: Instantiate the x86 access records and Stack laws from the byte memory model
status: open
labels: [stdlib,x86,memory,proofs]
area: heather-in-heather
milestone: [hih-memory-model]
created: 2026-10-21
updated: 2026-10-21
---

`lib/std/memory.hthr` (docs/byte-memory-design.md) is a library model so far.
Nothing in the machine model or the program logic uses it yet. x86's memory
is still an abstract `M` behind access records, and every `Stack<M>` law is
assumed by whoever builds the stack. This round connects the two
(design §6).

## Acceptance

- `Memory<BitVec(64), BitVec(8)>` instantiates `FetchAccess`,
  `ByteReadAccess`, `ByteWrites` and `LinuxIo`: reads through `read` as an
  `Option`, `executable` from the execute bit, `writable` as
  `Allows(Perm::writes, …)`, and `store` as `set_span` of the list's bytes.
  The x86 canonical-address rule lives in the instance's `perms`.
- `Stack<Memory<…>>` is built from a writable, readable region by proof.
  `stored`/`kept` and their companions come from `get_set_span`,
  `get_set_span_apart` and `BitVec::space_distinct`/`space_apart`, not from
  hypotheses.
- A `View` over a buffer's range for `Wp` (program-logic design §6.1, the
  third view). `Holds(v, m)` says the range's cells are the buffer's
  `get_span`. This is what `function-ir-buffer-state-edges` (S3, PR #117)
  needs to relate a buffer value to its bytes in memory.
- If one of these needs it: `Distinct` for a wrapping span (`k ≤ 2^n`
  from near the top), which needs modular injectivity of `iterate_increment`.
  Only the non-wrapping forms are proved today.

## Notes

- `next_rip(a, i)` is `BitVec::space(64).offset(a, i)` by definition. Both are
  `a.iterate_increment(i)`.
- x86's `ByteWrites.store` and Linux's read answers take a `List<BitVec(8)>`.
  The model's spans are vectors `[C; k]`. The instance needs a list-to-vector
  conversion (`[A; xs.len()]`), or a list-indexed `set_span`. Choose by which
  proofs read better.
