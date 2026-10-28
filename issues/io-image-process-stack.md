---
title: Map a stack region for compiled calls in the I/O image's profile
status: open
labels: [native,x86,memory]
created: 2026-10-22
updated: 2026-10-28
area: heather-in-heather
milestone: [hih-memory-model, hih-pl-wp]
---

The process image (`X86Memory::io_load`, `lib/std/os/linux/linux_x86_64_image.hthr`)
maps the file, the page and the frame. Linux also maps a stack and starts RSP
in it. Argv no longer needs that region: [[native-source-argv]] reads argc and
argv as `ArgvAt` cells at the entry RSP, beside `X86Memory::LoadedFrom(file)`,
and compiled code pushes nothing. What still needs it is code that calls: a
compiled function spills and calls through a `Stack<M>` (`DataRegion::stack`,
x86_64_byte_memory), so a compiled callee ([[wp-callee-from-lowered-function]])
or a procedure that makes calls ([[native-procedure-contracts]]) needs the
process's stack to be a data region the profile relies on from the entry.

## Scope

- The profile relies on a stack region below the entry RSP (its size a
  parameter, or Linux's minimum), and the loader maps it with the data
  permission. The `ArgvAt` cells above RSP stay as they are.
- The entry state's RSP and the region's top agree, so
  `DataRegion::stack` applies from the entry.
- What the region's lowest address is (Linux grows the stack on demand up to
  a limit) is a decision the issue owes: a fixed size relied on is the
  conservative reading.

## What it assumes from elsewhere

- **[[io-image-on-byte-model]]** owns the profile and loader. Assumed here:
  only that a profile's reliance can grow by a conjunct.
- **[[memory-model-machine-instances]]** owns `DataRegion::stack`.

## Log

- 2026-10-24: 2026-10-24: Wp runs stack items now ([[wp-stack-items]]); its call control (crates/elab/tests/fixtures/linux_wp_call.hthr) uses the I/O frame as the stack until this lands, and [[wp-callee-from-lowered-function]] needs the region for a compiled callee.
- 2026-10-26: Taken up by [[native-source-argv]] (round 6 of `docs/native-real-programs-plan.md`), which finishes it: argv is the first client of the stack region.
- 2026-10-27: [[native-source-argv]] did the argv part without a stack region: the ELF theorem (native_compile_elf) takes the entry memory as `X86Memory::LoadedFrom(file)` below 0x412000 and `ArgvAt` above it, at the entry RSP; compiled code reads argv through RSP saved at entry and pushes nothing. What stays here: the region a compiled callee spills into (`DataRegion::stack` from the entry), its size decision, and the loader mapping it.
- 2026-10-28: Re-scoped (tracker tidy): argv shipped without this region, so the title and scope now name what is left, the stack a compiled call spills and pushes into. Milestone `hih-tools` swapped for `hih-pl-wp`: the plan's tools inline their procedures and never touch a stack (`docs/native-real-programs-plan.md` §7), while a `Wp` callee from a lowered function does.
