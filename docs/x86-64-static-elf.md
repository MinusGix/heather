# Standalone x86-64 ELF export

`heather build-x86` writes a Linux executable directly from a supported
Heather function. The assembler and linker are absent from this path. It
shares source reflection, instruction selection, and source-to-x86
certification with `compile-x86`, which remains the assembly/FFI export path.

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
can grow to place multiple fragments when calls/data provide a customer.

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

The companion certificate checks each emitted code span against the model,
checks their layout, and equates the exact serialized file with the model
image. Both header and payload literals come from the actual byte vector
that will be written. The Rust serializer and allocator propose bytes;
ordinary kernel checking decides whether to accept them. Output is published
only after certificate acceptance, and existing output paths are refused.

## Environment boundary

The claim stops at a Linux exit request. Execution assumes that Linux maps
this valid image at the specified address, enters at e_entry, permits the
instruction fetches, and delivers the terminal 0F 05 transfer as syscall 60.
The host also supplies faithful file writes and executable permissions.
These are explicit environmental assumptions, not axioms installed in the
Heather library. We do not yet prove a memory-fetch relation connecting the
loaded image to each canonical instruction step, nor Linux syscall-entry
behavior. Typed register execution and exact byte placement are checked
separately at this milestone.

There is no verified CPU implementation, Linux loader, or Linux kernel here.
The next execution milestone is the loaded-memory/fetch bridge described in
`docs/x86-64-execution-boundary.md`, followed by stack/call composition and
memory-backed external interactions. Large argument/source literals retain
the known `bitvec::ofNat` conversion limitation tracked by
`issues/bitvec-ofnat-large-literals.md`.

## Validation

The native integration test builds with PATH pointing at an empty directory,
executes the resulting file, and checks both a normal result and truncation
to the Linux exit-status byte. The existing C-wrapper differential test still
checks 10005 input pairs through assembly export. Kernel negative controls
mutate 27 ELF header locations covering identity, entry, sizes, mapping,
permissions, and stack policy; the accepted header and every rejected mutant
are checked against the same Heather model. Host tests cover argument errors,
empty code, and the file-size bound.

## References

- [ELF gABI: ELF header](https://gabi.xinuos.com/elf/02-eheader.html)
- [ELF gABI: program loading](https://gabi.xinuos.com/elf/07-pheader.html)
- [Linux ELF loader](https://github.com/torvalds/linux/blob/master/fs/binfmt_elf.c)
- [Linux x86-64 syscall table](https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl)

The code contains original specifications of these format/platform facts.
