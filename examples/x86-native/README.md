# A Heather function in a native executable

From the repository root on x86_64 Linux with a C compiler/linker:

```sh
cargo build -p heather-cli
mkdir -p target/x86-native
(ulimit -v 8388608 -t 300; target/debug/heather compile-x86 \
  examples/x86-native/mix.hthr mix -o target/x86-native/mix.s \
  --cache-dir target/native-images)
cc -std=c11 -Wall -Wextra -Werror examples/x86-native/main.c \
  target/x86-native/mix.s -o target/x86-native/mix
./target/x86-native/mix
```

Expected output:

```text
mix(20, 22) = 81985529216486963; 10005 native cases passed
```

The command refuses existing assembly or certificate outputs. Remove those
outputs deliberately before rebuilding, or choose a fresh output name.

`mix.hthr` is the compiled program: it shares an addition, adds a full-width
constant, and XORs the results. The C file supplies `main` and checks boundary values and
10,000 deterministic pseudorandom pairs against unsigned C arithmetic.

## What `compile-x86` certifies

`compile-x86` compiles a function with `BitVec(64)` parameters (at most six)
and a `BitVec(64)` result, together with the word functions it calls,
through the verified lowering ([round 4 of the issue](../../issues/function-ir-verified-lowering.md)).
The body may use Add, Sub, AND, OR, XOR, `bitvec::ofNat` literals of any
size, `let`, calls, and tail-position matches on a test. A test is
`unsigned_lt_bit`, `signed_lt_bit` or `eq_bit` of words, `||`, `&&` and `!`
of tests, or a call of a `Bool` helper of words whose body is a test
(`branches.hthr`'s `composed` and `either`). Connectives and helpers become
conditionals on plain comparisons, each operand tested only where its
connective needs it. A source outside that fragment is refused, with a
message naming what it does not support.

The certificate does not reason about this particular program's
instructions. It reflects the source into a FunctionIR program and states:

- the program's lowering by `lower_program`, with the planner's placement,
  as a literal (`_lowers`, checked by evaluation);
- that the program evaluates to the source function at any arguments
  (`_agrees`). It is by `refl` when every match is on a comparison. A test
  through a connective or a helper has no conversion that commutes the
  source's `match` with the program's conditionals, so the certificate
  states the program's decision tree in source operations (`_expansion`),
  equal to the program by `refl` (`_expanded`) and to the source by
  `split_all` (`_expands`). Such a function cannot yet be called by another
  ([the issue](../../issues/function-ir-verified-decided-callees.md));
- the published bytes, a piece at a time (`_bytes`), and the exported
  function's offset (`_entry_at`);
- and `_returns`, which instantiates the theorem `compiled_returns`. Called
  at its label with its arguments in RDI, RSI, …, a return address at RSP
  and room on the stack below it, the code returns the source's value in
  RAX, keeps the callee-saved registers and RSP, and leaves the stack above
  the return address as it was.

The assembly is the whole program: each function's frame, body and RET,
with the exported symbol at its function's label. The platform ABI around
it (stack alignment, the C caller, the loader) is outside the proof.
`program.hthr` is a three-level example with calls in both arms of a
branch:

```sh
(ulimit -v 8388608 -t 300; target/debug/heather compile-x86 \
  examples/x86-native/program.hthr program -o target/x86-native/program.s \
  --cache-dir target/native-images)
```

Arguments arrive in RDI/RSI and the result leaves in RAX.

Proof support modules are bundled into the compiler. Source imports use the
normal loader with `lib/std`, `lib`, and additional `-L` directories. A source
module with a bundled library name must have identical contents. Optional
`--cache-dir` uses kernel-rechecked semantic images with exact build identity;
it does not enable the trusted declaration cache or stale-image replay.

## The other examples

Every `.hthr` here compiles the same way. `branches.hthr` holds nested
comparisons (`nested_true`, `nested_false`), connectives (`composed`) and a
`Bool` helper (`either`); the rest are call shapes: a call's result as the
next call's argument (`composition.hthr`), values live across calls
(`sharing.hthr`, `stack_save.hthr`, `multi_stack_save.hthr`,
`stack_local.hthr`), a leaf that writes several registers
(`multi_register.hthr`) and one callee called twice (`reused_callee.hthr`).
`crates/cli/tests/native_program.rs` and `native_branches.rs` compile each,
link it against a C reference and compare them on boundary and pseudorandom
inputs.

## Per-function certificates and `build-x86`: burned

Before the verified lowering, each function got a certificate generated for
its own instructions (structured, call and composition certificates over
`lib/certgen/ir_v1.hthr`), and `build-x86` wrote a static ELF executable
for a fixed fragment with a callee summary per call. Both were deleted in B2
(docs/native-program-logic-design.md §3.2). The last commit with them, their
recipes and this section's old text is `82521ea`. A direct executable comes
back on the verified path, as the compiled program inside a proved process
image (`issues/native-first-compiled-program.md`).

## Programs with input: burned

The programs that read stdin (`wc -l`, `wc` as a command, `tr`, `tr -s`,
`tr -d`) were proved by hand, a process library per program shape, and were
deleted in B1 (docs/native-program-logic-design.md §3.1). The last commit
with them, their build recipe and this section's old text is `189659d` (tag
`native-v0`). They come back as programs of an effectful source whose meaning
is an interaction tree, compiled by a compiler proved correct once
(`issues/native-first-compiled-program.md`). Their specs survive:
`lib/std/text/decimal.hthr` (what `%d` and `%7d` print) and `lib/native/stream_filter.hthr`
(a filter's fold and the counting lemmas).
