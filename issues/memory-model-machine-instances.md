---
title: Instantiate the x86 access records and Stack laws from the byte memory model
status: closed
labels: [stdlib,x86,memory,proofs]
area: heather-in-heather
milestone: [hih-memory-model]
created: 2026-10-21
updated: 2026-10-22
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

## Log

- 2026-10-22: Done. `lib/std/arch/x86_64/x86_64_byte_memory.hthr` and
  `lib/linux_x86_64_byte_memory.hthr`; tests in
  `crates/elab/tests/x86_64_byte_memory.rs`. The decisions, against the
  acceptance list:

  - **The machine's `M` carries its reliance.** `Stack<M>` states
    `writable`, `stored` and `keeps_code` for every `M`. Over
    `Memory<BitVec(64), BitVec(8)>` that includes memories with no
    permissions, where they are false. So `M` is `X86Memory(x)`: cells,
    permissions, and a proof of what the profile `x` (`X86Profile { relies }`)
    relies on of them. `x.at(m)` is the model's memory, and every access
    record goes through it: `read` as an `Option`, the execute bit,
    `Allows(Perm::writes, …)`, `set_span`. A store keeps the permissions and
    so the proof; a step that changes permissions proves the reliance again.
    (First pushed with the permissions fixed in the profile; Minus chose the
    carried reliance on 2026-10-22 so that allocation and mmap are steps, not
    a profile swap.)
  - **Canonical addresses**: `X86Profile::perm` gives no permission at or
    above `2^47`, whatever the memory's permissions say. Checked by evaluation at a literal
    profile (the first kernel-half address reads `None`), and refused as
    `Some`.
  - **Lists vs vectors**: `List::to_vector`, with one-cell
    `Memory::get_set_span_list` (a list's `r`-th element at its `r`-th address)
    and `get_span_agree` (spans of two memories agree when their cells do).
    The list form reads better wherever the machine names bytes by
    `nth`, which is everywhere.
  - **`DataRegion::stack`**: a `Stack` from `size` bytes below `2^47` that the
    profile relies on having `Perm::data()`. A fixture unmaps a page outside
    the stack and the same stack's laws apply to the new memory. `keeps_code` is the region never executing: an executable
    code byte cannot be one a stack store writes. A region that may execute
    is refused as a `DataRegion` (a negative control).
  - **Buffer view**: `DataRegion::buffer_view` knows a buffer's cells `v`, the
    buffer being `DataRegion::buffer(v)` (`Memory::buffer`'s shape), so the
    view threads cells and the shape stays fixed. `Holds` is pointwise, and
    `holds_span` gives the `get_span` equality. A word load reads
    `x86_word(q)`, the machine's packing (`immediate_from_bytes`), not
    `get_le`. Relating the two is not needed yet.
  - **Wrapping `Distinct`**: not needed. No span inside a canonical region
    wraps.
- 2026-10-22: Follow-up: [[io-image-on-byte-model]], the Linux process image as an `X86Profile`'s memory.
