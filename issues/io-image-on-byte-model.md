---
title: Load the process image into an X86Profile's memory
status: closed
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
`X86Profile` (`lib/std/arch/x86_64/x86_64_byte_memory.hthr`) now gives every
access record from `lib/std/machine/memory.hthr`, with a stack and a buffer view
whose laws come from the model's span lemmas.

## Scope

- Load an ELF image into an `X86Memory`: the file's bytes executable and
  readable, the page and frame as data regions (`DataRegion`) its profile
  relies on, the rest without permissions.
- The page and frame views restated over it, their store lemmas from
  `get_set_span_list`/`get_set_span_outside` instead of `io_store_offset`
  arithmetic, or retired in favour of `DataRegion::buffer_view` and a
  frame view over a `DataRegion`.
- `linux_wp`'s fixtures and the entry theorem moved to the new profile.

## What it assumes from elsewhere

- **[[memory-model-machine-instances]]** owns `X86Profile`, `X86Memory`,
  `DataRegion` and the buffer view. Assumed here: only that a memory carries
  a proof of what its profile relies on.
- **[[native-one-wp]]** owns `Wp` and the view interface.

## Log

- 2026-10-22: LANDED. `lib/std/os/linux/linux_x86_64_image.hthr`: the profile `X86Profile::io()` relies on the page (0x410000) and the frame (0x411000) being data and on nothing else; `DataRegion::io_page`/`io_frame` are its regions; `X86Memory::io_load(file)` maps the file at 0x400000 with `Perm::code()` (new in memory.hthr), the RW segment zero-filled, nothing else, and proves the code resident past a header (`io_load_resident`, `io_load_entry` at `io_entry()`) and both regions zero. The code is not in the profile but in the view: `View::with_code` + `X86Profile::with_code_sound` (stores on data keep code, `store_keeps_code`); `DataRegion::program_view` = buffer view + code (linux_x86_64_byte_memory). The page and frame views are retired, not restated: the page is the buffer view; the frame's word slots are a lemma over the buffer (`DataRegion::x86_word_stored`, from `get_set_span_list`). `lib/elf64_io.hthr` and `lib/linux_x86_64_views.hthr` deleted (IoMemory, io_store_offset arithmetic, the Stored kit). Fixtures moved: drain over the page, count over the frame; new `drain_entry` (the loaded process from its entry meets `drain(n)`) with a control (a 231-byte header is refused). Residue: a view over two regions at once (the old frame view knew page + slots) is [[wp-view-separating-product]]; the process's own stack (RSP, argv) is not mapped by the loader yet: [[io-image-process-stack]].
