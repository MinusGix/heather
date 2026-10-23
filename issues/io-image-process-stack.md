---
title: Map the process stack (RSP, argv) in the I/O image's profile
status: open
labels: [native,x86,memory]
created: 2026-10-22
updated: 2026-10-22
area: heather-in-heather
milestone: [hih-memory-model]
---

The process image (`X86Memory::io_load`, `lib/std/os/linux/linux_x86_64_image.hthr`)
maps the file, the page and the frame, and nothing else. Linux also maps a
stack and starts RSP in it, with argc, argv, envp and the auxiliary vector
above RSP. A compiled function spills and calls through a `Stack<M>`
(`DataRegion::stack`, x86_64_byte_memory), so the process's own stack must
be a data region its profile relies on before a compiled program can run
from the entry.

## Scope

- The profile relies on a stack region below an RSP the entry state names
  (its size a parameter, or Linux's minimum), and the loader maps it with
  the data permission; argv/envp/auxv are cells above RSP, readable.
- The entry state's RSP and the region's top agree, so
  `DataRegion::stack` applies from the entry.
- What the region's lowest address is (Linux grows the stack on demand up to
  a limit) is a decision the issue owes: a fixed size relied on is the
  conservative reading.

## What it assumes from elsewhere

- **[[io-image-on-byte-model]]** owns the profile and loader. Assumed here:
  only that a profile's reliance can grow by a conjunct.
- **[[memory-model-machine-instances]]** owns `DataRegion::stack`.
