---
title: A call passes at most six words, and a span is two of them
status: closed
labels: [native,x86,ir,design]
area: heather-in-heather
milestone: [nh-library,crypto-hash]
created: 2026-11-12
updated: 2026-11-14
---

A call of a compiled function passes its arguments in RDI, RSI, RDX, RCX, R8 and R9 and nothing on the stack, so a function takes at most six words. A span is two of them, its address and its length. The lowering has six places for a call's arguments (`argument_registers`, `lib/native/function_ir/function_ir_lower_calls.hthr`), a statement's call checks `arguments + 2 * lent <= 6` (`Layout::fits_lent`, `lib/native/native_compile.hthr`), and `compile-x86` answers that it "passes at most six, in registers" (`crates/cli/src/native/verified.rs`).

Where it already binds:

- `copy_window(out: span mut, text: span, from, end)` is exactly six, so a third word (a count apart from the window) had no room.
- A loop keeps its state in its parameters: `copy_span` is two spans, a count and an index. A loop over two spans with two more words of state does not fit, and a `runtime fn` has no other place for state than a parameter or a span.
- The hash's `compress(state, block)` is four words before any index or round count, which leaves two.

## Ways through

- Arguments past the sixth at the caller's RSP, as the System V convention has them. The frame already has the room laid out by one constant; the contract (`CalleePre`) would say where they are read, and an export's Rust declaration follows the same convention with no change.
- A span of words: the state a loop cannot hold in registers kept in a buffer the caller lends. This needs no new convention and is what the hash does with its eight state words anyway. It costs a load and a store for each use.

## Done when

A function of eight words is compiled and called from a function and from Rust, with its contract proved as the six-word ones are; control: nine is refused with the count named.

## What it assumes from elsewhere

- **[[function-frame-sized-by-use]]** owns the frame's size, which outgoing arguments add to.
- **[[native-register-moves-and-convention]]** owns the convention's statement.

## Log

### 2026-11-14: words past the sixth on the stack, eight at most

Built the first way through, System V's: a call passes its first six words
in RDI, RSI, RDX, RCX, R8 and R9 and the rest on its stack, the seventh just
above the return address (`lib/native/function_ir/function_ir_lower_calls.hthr`,
"Words past the sixth").

- **The contract.** `Stack::Passed(words, i, s)` replaces `ArgsIn(words,
  argument_registers(), s.gprs)` in `CalleePre`, `CalledOver` and
  `EnteredOver`: the words in the argument registers, then one a word from
  stack offset `i + 8` up (`Stack::Passes`). Six words or fewer read as
  `ArgsIn` did (`passes_of_args`). An export's Rust declaration is
  unchanged: `extern "sysv64"` passes the same way.
- **The caller** (`call_prog`): the caller-saved registers spilled as
  before, then RSP lowered by eight bytes a stack word (`stack_lower`, one
  `ADD RSP, imm8`, nothing for six words or fewer), each stack word stored
  from the register that holds it (`File::sources`), the first six moved
  into their registers, the CALL, RSP raised back (`stack_raise`), the
  spills reloaded. The stack words lie below the caller's frame, where its
  trail and saved slots are not.
- **The callee** (`function_opened`): before its frame, its entry loads the
  words past the sixth from RSP+8 and RSP+16 into R10 and R11
  (`stack_registers`), so its body starts with its parameters in
  `parameter_registers()` and the frame's displacements are unchanged. Not
  RAX: a call's result lands there, so a parameter in RAX is lost at the
  first call of a body that still reads it (the first build had RAX, R10,
  R11 and nine words; `compile-x86` of `stack_words.hthr` refused it at
  exactly that). R10 and R11 are spilled and reloaded around a call like
  the other caller-saved registers.
- **The limit is eight**: two stack words, the two free caller-saved
  registers. A ninth would need a home outside the registers the entry
  can load into (a slot of the frame, read in place), which is
  [[function-frame-sized-by-use]]'s ground.
- **Room**: `136` bytes a level where it was `120` (the frame's 112, two
  stack words and the return address), so every export's stated stack
  figure moves (`crates/linked/generated/*.s`), and the statement
  compiler's room per function is `144` where it was `128`
  (`Target::roomy`).
- **Refusals name the count**: a function of nine parameters ("the
  function has 9 parameters, and a function takes at most eight: six in
  registers and two on the stack"), a call of nine words ("it passes 9
  words, …", `function_ir_refusal.hthr`), and `compile-x86` ("takes 9
  words: compile-x86 passes at most eight, six in registers and two on the
  stack").

Done when, as built: `lib/_tests/native/function_ir/function_ir_lower_calls_tests.hthr`
lowers a program whose function of eight words calls another of eight and
is called from a function of two, each with `compiled_returns`' contract,
and refuses nine; `crates/cli/tests/native_program.rs`'s
`eight_words_are_called_from_rust` compiles `examples/x86-native/stack_words.hthr`
and calls it from Rust ten thousand times against a Rust reference.

Not done here: a statement's call (`Layout::fits_lent`,
`native_compile.hthr`) still passes six words at most, and the Rust
reflector's plain functions (`crates/elab/src/function_ir_source/program.rs`)
take six; `sha256_working.hthr`'s split of a round's second half into
`turn` and `set` can now be undone.

