---
title: Map a stack region for compiled calls in the I/O image's profile
status: closed
labels: [native,x86,memory]
created: 2026-10-22
updated: 2026-10-31
area: heather-in-heather
milestone: [hih-memory-model, hih-pl-wp, nh-procedures]
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
- 2026-10-26: Taken up by [[native-source-argv]] (round 6 of `docs/native/native-real-programs-plan.md`), which finishes it: argv is the first client of the stack region.
- 2026-10-27: [[native-source-argv]] did the argv part without a stack region: the ELF theorem (native_compile_elf) takes the entry memory as `X86Memory::LoadedFrom(file)` below 0x412000 and `ArgvAt` above it, at the entry RSP; compiled code reads argv through RSP saved at entry and pushes nothing. What stays here: the region a compiled callee spills into (`DataRegion::stack` from the entry), its size decision, and the loader mapping it.
- 2026-10-28: Re-scoped (tracker tidy): argv shipped without this region, so the title and scope now name what is left, the stack a compiled call spills and pushes into. Milestone `hih-tools` swapped for `hih-pl-wp`: the plan's tools inline their procedures and never touch a stack (`docs/native/native-real-programs-plan.md` §7), while a `Wp` callee from a lowered function does.
- 2026-10-28: [[native-data-capacity]] made the RW segment the program's
  size: `LoadedFrom(size, file)` agrees below `io_data_end(size)` and
  `ArgvAt` reads above it.
- 2026-10-31: Done (lib/std/os/linux/linux_x86_64_image.hthr, "The process's stack"). The
    process is a memory of `X86Profile::process(size, top, depth)`: what
    `X86Profile::io(size)` relies on, and `depth` bytes below `top` data.
    `StackPlaced(size, top, depth)` is where Linux puts it: above the segment,
    `top` canonical, and `depth` at most `io_stack_limit()`, the 128 KiB exec
    maps below the arguments before the program runs (fs/exec.c
    `setup_arg_pages`). The size decision the issue owed: a fixed depth the
    process relies on, up to that 128 KiB, never the on-demand growth (what a
    fault would map is not mapped when the run reads). `DataRegion::process_data`
    and `DataRegion::process_stack` are the two regions;
    `process_stack_entry` puts the stack's top at the entry RSP and
    `process_stack_push` a CALL's return address in its top word, so
    `DataRegion::stack` applies from the entry; `process_stack_keeps_data`:
    a word stored in the stack keeps the segment's `Holds`. The loader
    `X86Memory::process_load` maps the stack with the data permission and is
    `LoadedFrom` the file (`process_load_loaded`), so the ELF theorem's
    premises are not vacuous. `LoadedFrom` and `loaded_entry` take any profile
    (explicitly, [[implicit-from-record-parameter-type]]). The ELF
    theorem (`Source::elf_simulates`/`elf_file_simulates`), cat's theorems and
    every `write-elf` certificate (`<s>_simulates`) quantify over `top`,
    `depth` and `StackPlaced`, with `rsp: read_gpr(Rsp, s.gprs).toNat() =
    top`; the compile pushes nothing yet, so the proof uses only the segment.
    Probes: lib/_tests/std/os/linux/linux_x86_64_image_tests.hthr. The
    client is [[wp-callee-from-lowered-function]] (a compiled callee spills
    into this stack); a Wp view over segment and stack at once is
    [[wp-view-separating-product]].
