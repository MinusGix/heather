# Standalone x86-64 ELF export

`heather build-x86` writes a Linux executable directly from a supported
Heather function. The assembler and linker are absent from this path. It
shares source reflection, instruction selection, and source-to-x86
certification with `compile-x86`, which remains the assembly/FFI export path.

The separate [call profile](x86-64-calls.md), selected with `--callee`, adds
three code fragments and an owned writable stack page. The read-once profile,
selected with `--read-loop`, reuses that image with the page as an input
buffer: it reads stdin once, runs a certified counting loop and exits with the
count, and its claim is a Linux trace over fetched execution
([its design](native-first-program-design.md)). The profile below
describes the default inline build.

## First executable profile

The input is the existing two-argument, 64-bit pure arithmetic fragment. Two
`--arg` values are baked into the entry sequence; this is not runtime argv
parsing. Decimal, `0x` hexadecimal, and `0b` binary arguments are accepted.
The generated process initializes RDI/RSI, executes the certified function
body inline, copies RAX into RDI, sets RAX to 60, and executes SYSCALL. No
stack operations or RET are used. The parent observes the low eight bits of
the computation as the process exit status.

The ELF profile is little-endian ELF64, EM_X86_64, ET_EXEC. A single PT_LOAD
maps the entire file read/execute at `0x400000`; the entry address is
`0x4000b0`, corresponding to offset 176. A second program header,
PT_GNU_STACK, requests a read/write, non-executable stack. File and memory
sizes agree. The image has no sections, interpreter, relocations, writable
data, or dynamic dependencies. Total file size is bounded to 65535 bytes,
including the 176-byte header area. Code must be nonempty.

This is an intentionally restricted profile, not a general ELF parser or an
object-file linker. The layout layer is separate from source reflection and
also has a first multi-fragment customer in the call profile.

## Checked claims

`lib/elf64.hthr` specifies the exact header profile, including field offsets,
permissions, mapping base, and entry. `StaticElf64Image` carries nonempty-code
and file-size proofs. Its entry-byte theorem proves that dropping the header
area from the serialized image yields exactly the supplied code.

`lib/linux_x86_64_entry.hthr` proves argument initialization and exit-register
setup using the existing canonical x86 ExecuteBlock relation. A
`LinuxInlineTrace` composes the entry, compiled body, and exit-setup stages,
ending in a `LinuxExitRequest` whose full status value equals the source
function applied to the selected arguments. The generator constructs a
concrete valuation and a RegionHolds witness, so this process theorem has no
remaining caller-supplied graph assumption. Its initial machine state and
memory type remain arbitrary.

`lib/elf64_load.hthr` interprets that restricted image as file-backed RX bytes
at absolute 64-bit addresses. The address's upper 48 bits select the fixed
mapping window; the lower 16 bits select a byte within the file. Reads outside
the window or past the file end are absent. There is no zero-fill tail because
this profile requires p_memsz = p_filesz. This is a restricted view of the
process's memory; it leaves the unused stack, page padding, and other mappings
unspecified rather than claiming Linux lacks them.

The generated `*_loaded_image` proves that the memory bytes are the checked ELF
file. `*_loaded_trace` starts at its entry with those bytes as memory and with
arbitrary GPRs and flags. It carries an `ExecuteFetchedBlock` trace through entry,
body, and exit setup, a fetched witness for the terminal SYSCALL bytes, and a
`LinuxExitRequest` whose full status equals the source function's result.
Each ordinary step uses the same memory and RIP for fetching and canonical
execution; syscall execution itself remains outside the architectural slice.

Fetch certificates contain structural `ReadableBytes` witnesses for byte values,
execute permission, and nonwrapping address advancement. `fetched_result` proves
that these witnesses agree with the executable `fetch_instruction_bytes` reader.
The producer proposes binary address literals and flattened successor states;
separate checked facts establish each read and equality to the canonical
successor. Naming byte facts and execution suffixes keeps composition from
repeatedly expanding an entire prefix's memory and register computations.

The companion certificate checks each emitted code span against the model,
checks their layout, and equates the exact serialized file with the model
image. Both header and payload literals come from the actual byte vector
that will be written. The Rust serializer and allocator propose bytes;
ordinary kernel checking decides whether to accept them. Output is published
only after certificate acceptance, and existing output paths are refused.

## Environment boundary

The claim stops at a Linux exit request. Execution assumes Linux supplies the
specified file-backed RX mapping and entry state, and delivers the terminal
0F 05 transfer as syscall 60. The host also supplies faithful file writes and
executable permissions. These are environmental assumptions, not axioms
installed in the Heather library. Within that supplied mapping, byte fetch,
supported decoding, typed execution, and the source result are now connected.

There is no verified CPU implementation, Linux loader, or Linux kernel here.
The call profile extends this boundary with fetched near CALL/RET and byte-backed
return slots. General call graphs and memory-backed external interactions remain
future work; this loaded view suffices for the register-only inline profile.
Full-width argument/source literals are supported; `bitvec::ofNat` conversion
now performs work bounded by the width (see `issues/bitvec-ofnat-large-literals.md`).

## Validation

The native integration test builds with PATH pointing at an empty directory,
executes the resulting file, and checks both a normal result and truncation
to the Linux exit-status byte. The existing C-wrapper differential test still
checks 10005 input pairs through assembly export. Kernel negative controls
mutate 27 ELF header locations covering identity, entry, sizes, mapping,
permissions, and stack policy; the accepted header and every rejected mutant
are checked against the same Heather model. Loaded-memory controls reject
changed payload bytes, wrong entry/base addresses,
truncated spans, altered syscall bytes, non-executable access, and an unadvanced
successor RIP. Positive checks
cover header/code addressing, bounds, a neighboring address window, and neutral
byte values. Host tests cover argument errors, empty code, and the file-size bound.

## References

- [ELF gABI: ELF header](https://gabi.xinuos.com/elf/02-eheader.html)
- [ELF gABI: program loading](https://gabi.xinuos.com/elf/07-pheader.html)
- [Linux ELF loader](https://github.com/torvalds/linux/blob/master/fs/binfmt_elf.c)
- [Linux x86-64 syscall table](https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl)

The code contains original specifications of these format/platform facts.
