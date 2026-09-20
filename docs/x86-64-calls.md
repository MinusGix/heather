# First certified calls

`build-x86 file.hthr caller --callee leaf --arg 20 --arg 22 -o program`
compiles a forwarding caller and an arithmetic leaf to distinct code fragments.
The forwarding source caller has two parameters and returns `leaf(left, right)`
with its original arguments in order. The [live-local extension](x86-64-call-frames.md)
also supports `leaf(left, right) XOR (left XOR right)`. The
[reusable-summary extension](x86-64-call-summaries.md) supports two calls with
a live caller local and a callee-owned frame. The
[straight-line composition extension](x86-64-call-composition.md) accepts
arithmetic and computed/reordered arguments around repeated calls. The
[callable composed profile](x86-64-composed-callers.md) adds a reusable caller
summary and native register preservation with `--callable-caller`. The leaf supports the existing straight-line
BitVec(64) arithmetic fragment. Both source identities come from elaborated
terms; the certificate checks the caller/callee equation against the source.
`--callee` explicitly opts that additional function into this initial driver.
It is a temporary driver interface, not the planned Heather runtime generator.

The entry calls the caller, which calls and returns from the leaf before
returning to the entry. These are actual E8 rel32 and C3 instructions, not
inlining or an unproved return shim. The leaf is placed before the caller to
exercise a negative signed displacement. Each displacement is relative to the
end of its five-byte CALL, following Intel's [CALL/RET specification](https://cdrdv2-public.intel.com/671110/325383-sdm-vol-2abcd.pdf).

## Convention and stack

The initial internal convention puts arguments in RDI/RSI and the result in
RAX. RAX, RCX, RDX, RDI, RSI, R8–R11, and arithmetic flags may be clobbered.
RBX, RBP, and R12–R15 are preserved. This is an internal choice; no foreign C
ABI adapter or annotation is implemented here.

The ELF supplies a separate zero-filled RW PT_LOAD page at 0x401000, and the
entry sets RSP to its top at 0x402000. Code remains RX and fits below 0x401000.
The stack is non-executable. Linux's initial stack is unused; there is no argv
processing. PT_GNU_STACK still requests a non-executable process stack.

RSP is 16-byte aligned before each CALL. The entry's return address occupies
0x401ff8–0x401fff. The wrapper reserves eight bytes for alignment, then the
leaf's return address occupies 0x401fe8–0x401fef. The wrapper releases its slot
before returning; the final RSP is 0x402000. The live-local extension uses
the alignment slot for a value retained across calls. The two-call extension
gives the leaf its own eight-byte slot below its return address. General call
graphs, recursion, indirect calls, variadic functions, and arbitrary locals or
spills remain outside the supported source fragment.

## Checked boundary

`x86_64_calls` adds normal-path near CALL/RET semantics around the existing
machine state. RSP is an ordinary register. Return addresses are eight
little-endian bytes in memory, with per-byte access and address-wrap premises. The access policy is fixed
for this execution profile; stack writes change bytes, never permissions.
RET reads the bytes that CALL wrote; it does not consume a separate logical
return-address stack. Ordinary instructions reuse the existing canonical
execution relation. A denied memory access admits no normal execution proof;
this slice does not yet describe the exception outcome or CET shadow stacks.

The producer lays out uniquely named, byte-aligned entry/leaf/caller fragments,
rejects unresolved or duplicate symbols, signed-rel32 overflow, and overlap
with the stack page. The certificate connects the emitted ELF header and code
to the restricted image model, checks each fetched instruction against those
bytes, and follows the execution order through calls and returns. The leaf
exports a result/return/RSP/memory-effect/preserved-register contract; the caller's
result proof uses that contract field. A reusable summary now proves the
leaf postcondition over arbitrary entry states and valuations. Each call site
still supplies actual per-instruction fetch/access evidence and checked state
equalities; summary execution is composed into the surrounding trace.

The certificate names literal intermediate addresses and individual stack-byte
writes and reads, then joins them with equality proofs. Backward CALL targets
use a proved modular-add/subtract law. Concrete add/sub results are checked with
width-bounded ripple arithmetic and transported to the canonical operations by
proved bridge lemmas. This replaces the initial small increment/decrement chains
and avoids normalizing a sign-extended displacement by unsigned iteration.
The transport adds no axioms or kernel rules.

The final request carries the full source result in RDI and Linux's exit
syscall number in RAX. The terminal syscall bytes are fetched from the same
memory. Linux reports the result's low eight bits as process status.

Linux loading these PT_LOAD segments, initial long-mode execution without CET,
faithful output writing, and syscall delivery remain environment assumptions.
The memory view models the owned stack page and file bytes, not all Linux
mappings, page rounding, concurrency, interrupts, or a verified CPU.

## Validation

The example produces a 334-byte ELF and exits with status 197 for arguments
20 and 22. It includes a backward CALL displacement, two actual returns, and
a full-width hexadecimal constant in the leaf. The native integration test
builds with an empty PATH, checks the three program headers, runs the file,
and requires the loaded-execution, callee-contract, syscall-fetch, and final
stack-restoration claims in its companion certificate.

Focused controls check signed displacement limits, duplicate/unresolved
symbols, code/stack overlap, unsupported source wrappers, denied stack access,
underflow, noncanonical addresses, altered CALL/return bytes, and an executable
stack-header mutation. Stack-store checks also use a neutral byte value.
