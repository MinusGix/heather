---
title: Grow a native arena with mmap as a Linux call
status: open
labels: [native,memory,linux]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-02
updated: 2026-11-02
---

A native arena today is a `Source` buffer in the data segment, sized when the
program is written (docs/native-heap-arena-design.md §1, §5). Growing one at
run time is `mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS,
-1, 0)`.

## Scope

- `MmapCmd` in `lib/std/os/linux/linux_calls.hthr` with its answers (an
  address, or `ENOMEM`, which is the arena's defined exit).
- A `CallShape` for it in `Source`, and a buffer the compiled code reaches
  through the address in a word instead of a fixed data-segment offset. That
  is new to the compiler: every buffer's address is fixed by the layout today.
- What the compiler's theorem then needs about two regions of machine memory
  at once: [[wp-view-separating-product]]'s footprints, and the permission
  change `docs/byte-memory-design.md` §7 describes.

`native_arena`'s laws are about the arena's bytes wherever they live, so
nothing there changes.

## Done when

`sort` runs on an input larger than its data-segment arena by mapping more,
and still exits with its message when `mmap` fails.
