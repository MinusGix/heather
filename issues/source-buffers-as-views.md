---
title: One notion of buffer in Source: static, borrowed, arena and frame storage as views
status: open
labels: [native,design,memory,function-ir]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-10
updated: 2026-11-10
---

A `Source` buffer is a numbered static slot in the ELF's data region
(`Source.buffers`, `Layout`). Three rounds have each needed something else
and each would build it separately:

- the arena: a line is a span of the arena buffer, so `Bytes` must lower as
  a view (buffer, offset, length) and not only as a whole buffer
  ([[runtime-fn-arena-lists]], log of 2026-11-02);
- an export: the source span and the hash state are memory the caller owns,
  at an address that arrives in a register ([[native-library-exports-design]]);
- a procedure: local scratch is a block of its frame.

## Scope

- A buffer as an address held in a word plus a capacity. Static, borrowed,
  arena and frame buffers are instances that differ only in where the
  address comes from and who may write.
- `Target::Placed`/`Held` and the byte nodes' lowering (`BufferLoad`,
  `BufferStore`) over an address word; `Layout`'s static buffers as the
  instance with a literal address.
- Footprints as span sets (`lib/std/data/set/span_set.hthr`): two views are
  apart when their spans are, decided by the endpoints.
- `rt`'s `Bytes` held as a view, so a slice costs no copy.

## Done when

One program reads a static buffer, a borrowed span and an arena line
through the same nodes and the same lowering case, with a negative control:
a store through a read-only view is refused by the judgment.

## What it assumes from elsewhere

- **[[native-library-exports-design]]** decides whether this is the notion
  to build. Assumed here: only that it is asked the question first.
- **[[function-ir-buffer-state-edges]]** owns byte nodes in S4 with
  registers held across them.
- **[[state-location-and-frame-kit]]** owns point updates of a store.
