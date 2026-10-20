---
title: Stream filters whose output is longer than their input
status: open
labels: [x86,native,design]
area: heather-in-heather
created: 2026-10-01
updated: 2026-10-01
---

The stream filter (docs/native-stream-filter-design.md §1) emits at most one
byte per input byte, written in place behind the read cursor in the one RW
page. A filter whose output can be longer than its input does not fit:

- `unix2dos` emits two bytes for a newline.
- `dos2unix` holds a `\r` until it sees the next byte, then emits both when
  that byte is not `\n`.
- Anything that expands escapes, or `cat -A`, has the same problem.

What it needs: a step that emits up to `k` bytes (an `emit: List<BitVec(8)>`
bounded by `k`, or `k` options), and somewhere to put them. The write
cursor's invariant (`o ≤ i`, elf64_read_filter's `FilterAt`) is what fails.
Either reading at most `4096 / k` bytes per chunk into the page's tail with
the output written from its start, or a second writable region
(`IoMemory`'s page is one 4096-byte page, elf64_io).

Related: [[native-loop-emitting-stores]], where the user chose the
one-byte, in-place shape for step 2 (2026-10-01).
