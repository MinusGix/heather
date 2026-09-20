# Native byte-buffer cursor recognizers

`compile-x86 --buffer-cursor` exports a source-defined word classifier inside a
checked byte-buffer cursor operation. The same compiled function handles input
supplied after compilation. There is no parser heap, expression tree, or runtime
proof allocation in this profile.

```sh
cargo build -p heather-cli
(ulimit -v 6291456 -t 300; target/debug/heather compile-x86 \
  examples/x86-native/recognize_plus.hthr recognize_plus --buffer-cursor \
  -o target/recognize.s --cache-dir target/native-test-images)
cc -std=c11 -Wall -Wextra -Werror examples/x86-native/recognize_main.c \
  target/recognize.s -o target/recognize
./target/recognize 'x+z' 1
# match 2
./target/recognize 'x+z' 0
# mismatch 0
./target/recognize '' 0
# end 0
```

Output paths must be fresh. The driver copies up to 256 input bytes into a local
array and accepts an optional decimal cursor. It formats the returned status and
cursor into another local array and calls `write`. The generated assembly owns
the bounds check, memory load, character classification, and cursor update.
The driver contains no recognizer and calls no allocator.

## Source and runtime interface

The classifier has the existing native source signature:

```heather
fn recognize_plus(byte: BitVec(64), cursor: BitVec(64)) -> BitVec(64) {
    bitvec::bxor(64, byte, bitvec::ofNat(64, 43))
}
```

Zero accepts; any nonzero value rejects. The first argument is a zero-extended
byte, and the second is the incoming cursor. Classifiers use the existing
checked arithmetic source lowering. The source function is compiled once and
is never evaluated by the host input adapter.

The exported machine interface is compatible with the host adapter's declaration:

```c
struct cursor_reply { uint64_t status, next; };
struct cursor_reply recognize_plus(const unsigned char *base,
                                  uint64_t length, uint64_t cursor);
```

RDI supplies the base, RSI the length, and RDX the cursor. RAX/RDX return
status/next. Status 0 means match and advances by one; status 1 means mismatch
and preserves the cursor; status 2 means cursor >= length and preserves it.
Unsigned comparison handles high-bit cursors correctly. The code reads exactly
one byte on the in-bounds path and no byte on the exhausted path. Embedded NUL
and high bytes work through the machine interface; the command-line adapter
uses argv strings and consequently stops at NUL.

Storage ownership and the truthful length belong to the caller. The generic
certificate requires that the selected address is readable, low-canonical,
and formed without address wrap. It makes no readable-byte demand on the
exhausted path. The 256-byte capacity is the example adapter's bound; the
machine operation itself works for any buffer satisfying those premises.

## Checked boundary

`byte_cursor.hthr` defines the buffer/cursor operation independently of register
placement. `arch/x86_64/buffer_cursor.hthr` adds the restricted MOVZX
`RDI, byte [RDI + RDX]` form and short JNB semantics; ordinary arithmetic,
comparison, TEST, JZ and JMP reuse existing models. The new encoding follows
[Intel's instruction reference](https://cdrdv2-public.intel.com/868141/253667-089-sdm-vol-2b.pdf).

Each generated certificate checks:

- The exported byte sequence against the selected ordinary instructions and
  restricted load/branch encodings.
- The source classifier refinement for arbitrary loaded bytes and cursors.
- The unsigned guard and conditional load permission, plus execution of the
  selected instruction path.
- Status/cursor agreement with the buffer operation, unchanged memory, and
  preservation of RSP, RBX, RBP, and R12–R15.
- Every static branch target and arrival at the appended return instruction
  for an arbitrary code base, on every path.

As with ordinary assembly export, assembler/linker behavior, code fetch, the
host's ABI call/return adapter, and the appended RET remain external boundaries.
This profile is not a standalone ELF loaded-memory certificate. It refuses a
classifier whose body exceeds the bounded forward short-branch layout, and it
does not add indirect calls, recursive parsers, or general memory operands.

## Validation and next step

`native_buffer_cursor` builds one function and exercises runtime strings,
65,536 byte/cursor combinations, memory preservation, high-bit cursors, and
reads adjacent to an inaccessible guard page. It also checks the certificate
standalone and rejects mutations to emitted bytes, branch targets, cursor
claims, read-permission evidence, and the source classifier.

This is the first primitive toward the showcase calculator. Compiling decimal
runs and then parser sequencing/alternatives requires further loop/control-flow
and parser representation work; the existing list-based combinator library is
not yet lowered by this export profile.

[Decimal runs](../issues/x86-buffer-decimal-parser.md) track the next executable
parser milestone.

Final validation on 2026-09-19: plain `scripts/test` passed **2833 passed,
0 failed, 5 ignored**. Proof and process limits are unchanged. The existing CLI
unit-test target remains near its CPU limit; its
[headroom follow-up](../issues/x86-composed-summary-test-cpu-margin.md) stays open.
