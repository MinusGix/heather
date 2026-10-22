---
title: Load the process image into an X86Memory profile
status: open
labels: [native,x86,memory,proofs]
area: heather-in-heather
milestone: [hih-memory-model]
created: 2026-10-22
updated: 2026-10-22
---

The Linux process profile (`io_linux()`, `IoMemory` in `lib/elf64_io.hthr`)
is a memory of its own: a fixed image with a page and a frame, its own
`io_read`, `io_store` and `IoWritable`, and the page and frame views
(`lib/linux_x86_64_views.hthr`) prove their store laws over it by hand.
`X86Memory` (`lib/std/arch/x86_64/x86_64_byte_memory.hthr`) now gives every
access record from `lib/std/memory.hthr`, with a stack and a buffer view
whose laws come from the model's span lemmas.

## Scope

- Load an ELF image into an `X86Memory` profile: the file's bytes
  executable and readable, the page and frame as data regions
  (`DataRegion`), the rest without permissions.
- The page and frame views restated over it, their store lemmas from
  `get_set_span_list`/`get_set_span_outside` instead of `io_store_offset`
  arithmetic, or retired in favour of `DataRegion::buffer_view` and a
  frame view over a `DataRegion`.
- `linux_wp`'s fixtures and the entry theorem moved to the new profile.

## What it assumes from elsewhere

- **[[memory-model-machine-instances]]** owns `X86Memory`, `DataRegion` and
  the buffer view. Assumed here: only that a profile's permissions are fixed
  across a run.
- **[[native-one-wp]]** owns `Wp` and the view interface.
