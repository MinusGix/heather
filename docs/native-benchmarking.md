# Benchmarking the code the compiler emits

The other harnesses measure the compiler (`docs/benchmarking.md`,
`docs/frontend-benchmarking.md`, `docs/cloud-benchmarks.md`). This one
measures what it *produces*: how fast linked Heather runs, against Rust
references for the same work, and what compiling it costs. The SHA-256 of
`lib/native/crypto/` is the standard case, because it is a whole program
with a proof of agreement with its specification
(`lib/native/crypto/sha256_stream_agreement.hthr`) and a well-known best
answer; the linked scanner rides along. Owning issue:
`issues/linked-sha256-speed.md`.

## Running it

```
scripts/bench-native                 # measure everything and print the table
scripts/bench-native --check         # compare against the snapshot
scripts/bench-native --save          # record a new snapshot
scripts/bench-native --quick --no-compile   # iterate: shapes, a minute
scripts/bench-native --no-count      # skip callgrind
```

Always through the script, never `cargo bench`: it builds the bench at both
profiles and the release compiler first, then runs everything under the
caps (`ulimit -v`, `-t`, `-c 0`). The bench is
`crates/linked/benches/native/` (`harness = false`); the script drives its
three modes (`time`, `count`, `report`), and the binary's header says what
each does. A full run is dominated by the cold compiles: each SHA-256
export is compiled from an empty image store, which takes minutes. `--quick`
compiles only `sha256_compress`.

## What the table says

**SHA-256 compression, ns per block**, the minimum of the samples, at
opt-level 3 (the release profile) and opt-level 0 (the dev profile), four
implementations:

| row | what it is |
|---|---|
| linked | `heather_linked::sha256::block::compress_spans`: one call into compiled Heather (`Sha256::compress`) |
| mirror | `benches/native/mirror.rs`: the Heather source in Rust, function for function |
| textbook | `benches/native/textbook.rs`: everything in locals, as a textbook writes it |
| sha2 | the `sha2` crate's `compress256`, with the backend it chose (the CPU's SHA extensions where present, else its scalar code) |

The linked row is the same assembly in both columns; it is there in the
opt-level 0 column so a reader sees that, and because the Rust around the
call differs.

**SHA-256 stream, MB/s**: one MiB and 37 bytes hashed whole (the padding
takes a second block), the same four. The linked row is
`heather_linked::sha256::stream::digest`, every byte of the work compiled
Heather.

**Linked compression, counted**: instructions executed inside
`sha256_compress` per block, exactly (callgrind over 200 blocks,
`--toggle-collect=sha256_compress`), and calls per block. **This is the
optimizer's counter**: exact, repeatable, the same on every x86-64 machine,
so a pass that lands moves it and says by how much. The breakdown joins
callgrind's per-instruction counts with `objdump -d -M intel` of the same
binary and sorts each instruction into a kind (`frame loads/stores` is a
`mov` through `[rsp…]`: registers saved round a call, mostly; `byte
loads/stores` is the span traffic; `call/ret/frame` includes the stack
pointer's adjustment). The kinds are in `callgrind.rs`. Without valgrind
the section says "not measured" and nothing fails.

**compile-x86, seconds**: wall time of `heather compile-x86` for each
SHA-256 row of `crates/linked/generated/EXPORTS.tsv`, as `scripts/linked`
runs it (release binary, generator, certificate checked). *Cold* is against
an empty native-image store of the row's own, so it includes elaborating
and imaging every module the row imports; *warm* is the same compile again
over that store, which is generation and the certificate check. Rows run
one at a time. These are wall-clock times of a multi-threaded process and
are the noisiest numbers here.

**Scanner over `lib/**/*.hthr`**: MB/s of the linked scanner
(`heather_linked::scanner::Scanner`, every token) and of the Rust lexer
(`heather_syntax::lexer::lex_rust`), release; and instructions per byte of
each, counted as callgrind's total for cutting the corpus minus its total
for only reading it.

## The mirror, and why it is written that way

The question the table answers first is *code gap or compiler gap*: how
much of the distance to the textbook is the shape of our source (a context
of big-endian bytes in memory, every word read a byte at a time under a
length test, the working variables moved through memory every round, the
round constant found by halving), and how much is what our compiler does
with that shape. The mirror is that shape in Rust, so LLVM's opt-level 3
over it is a bound on what a good compiler gets from our source, and
opt-level 0 over it is roughly what a compiler gets with no optimization.

So the mirror follows the Heather source exactly: one Rust function per
`runtime fn`, the span words of `stored_words.hthr` as functions, a
`decreases` function that calls itself last as a loop (our compiler makes
it one too). Before anything is timed, `check` in `main.rs` holds the
mirror to the linked code **byte for byte**: the whole context after
`init`, after each `update` of a message cut in parts, after `finish`, and
after `compress`; and every implementation to the `sha2` crate's digest.
When the Heather source changes, the check fails until the mirror follows
it, which is what keeps the mirror's numbers about our source.

Two differences remain and are deliberate: Rust indexes a slice with its
own bounds check after the source's length test (LLVM removes some), and the
mirror's span accessors are free functions that LLVM inlines at opt-level
3. Reading the two columns together says how much inlining is worth.

## The snapshot

`crates/linked/benches/baseline.tsv`, recorded on the cloud box (the
reference environment, `docs/cloud-benchmarks.md` §1). `env` rows name the
cpu, rustc, commit, date and the `sha2` backend; `measure` rows are
`key value unit`, the key saying the profile and case
(`time/release/sha256/block/linked`), the count
(`count/sha256/block/instructions`) or the compile
(`compile/sha256_compress/cold`). Only minimums (and best MB/s) are recorded.

`--check`:

| what | fails when | why |
|---|---|---|
| the compression's count (`count/sha256/block/instructions`) | it rose at all | exact and deterministic over fixed input: a moved counter is a change in the emitted code, not noise |
| the scanner's count (`count/scanner/…/per-byte`) | it rose by more than 1% | exact too, but its input is `lib/`, which every library round edits; the mix of tokens drifts by fractions of a percent |
| a linked time | ≥ 1.25× slower on the snapshot's cpu and rustc | the kernel suite's threshold and reasons (`docs/benchmarking.md`) |
| a reference time, a compile time | never; printed | the references are Rust's, not ours, and compile times are the noisy wall clock |

Any moved counter is printed, and a fall is a hint to re-record. A run on
another cpu or rustc compares only the counters and exits 3
(`shape-only`), as the kernel suite does.

**Re-record** (`--save`) when a change to the lowering, the emitter or a
linked module moves the counter, and say so in the commit with the old and
new instructions per block; when the machine or toolchain changes; or when
the mirror changes because the source did. A pass that lands names its
counter's move in its PR: that is how the optimizer's progress is read.
