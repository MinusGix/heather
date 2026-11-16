# Programs that do their own I/O: a surface `runtime fn` over `Io` to an ELF

Status: **proposed (2026-11-15); D1–D3 answered by Minus the same day (§5)**, thread "Compile Heather programs with their
own I/O". It finishes item 4 of `docs/language/effects-capabilities-design.md`
§6 ("`runtime fn main` publishing a `Source` that `write-elf` compiles") and
extends that note's §8 (the computation layer `ETm`/`ELoop`), not re-deriving
it. Read `docs/compilation-vision.md` first. Decisions that set language
design are in §5 and are Minus's; everything else reads surface that exists
today.

## 0. In one page

What a user should be able to write, and nothing else:

```heather
// Exit 0 when stdin is UTF-8, 1 when it is not.
runtime fn main(mut io: Io) → Partial(Mutated<Io, u64>) {
    let mut input: [u8; 1048576] = [0; 1048576];   // static memory (§5 D2)
    let mut n: u64 = 0;
    let mut going = True;
    while going {
        let r = io.read_into(Io::stdin(), input, n, 1048576 - n);   // read at offset n (§4.1)
        input := r.buf;
        if r.result = 0 { going := False } else { n := n + r.result }
    }
    let ok = utf8_valid(input, 1048576, n, 0);   // a `runtime fn` lent the span
    Pointed::ret(Mutated(io, if ok = 1 { 0 } else { 1 }))
}
```

and then

```
heather write-elf demo.hthr -o validate      # `main` by default; `f::source` names another
```

gives a standalone x86-64 Linux executable, no C `main`, whose certificate
states, with no proof written for this program:

- `main::source_elf_simulates`: the process Linux makes of the file
  simulates the `Source` (the compiler's theorem, as for every `write-elf`
  program today, `native_compile_elf`);
- `main::reads`: that `Source`'s tree, read against **any** world, is
  `main` up to silent steps (`Io::Reads`, the agreement
  `docs/language/effects-capabilities-design.md` §3 states for every program);
- and whatever the user proved about `main` itself (that it exits 0
  exactly when the bytes are `utf8::encode(s)` for some `s`) is then a
  statement about the binary.

Every piece of the middle exists in some form today. The `ETm`/`ELoop` layer
lowers a computation over `Io` with loops and calls of compiled span
functions to a `Source`, soundly, and `write-elf` compiles any `Source`. What
is missing is the front: the reflector does not read a `while` over `Io`, no
generator publishes the lowered `Source` and its theorem, and three things a
real program needs (a read at an offset, a branch whose arms call Linux,
constant bytes to write) have no node. §1 lists the gaps; §2 to §4 design
each; §6 orders the rounds.

## 1. Where things stand

Built (with the file to read):

| Piece | Where | State |
|---|---|---|
| `Io`, `mut self`, `Io::Reads`, `reads_bind`, `reads_iter` | `linux_world`, `linux_world_co` | built |
| `while` with no measure over `Partial` | parser (`imperative.rs`), sequencing design §18 | built: `Iterate::then(init, step, k)` |
| `ETm` (`Pure`/`Let`/`Invoke`/`Lend`), `ETm::sem` | `rt_io.hthr` | built |
| Reflector, loop-free bodies only | `rt_io_reflect.hthr` | built; refuses loops and branches over the world |
| `ETm::lower`, `lower_reads` | `rt_io_lower.hthr` | built |
| `ELoop` (`Seq`, `While`), `ELoop::lower_reads` | `rt_io_loop.hthr` | built |
| `Lend`: a computation calls a span `runtime fn` that may write | `rt_io.hthr`, PR #581 | built as a term; not reflected |
| `tr` as one `ELoop` term, through `write-elf`, held to GNU tr | `rt_io_lend_tests.hthr`, `native_tools.rs` | built; since round 2 the `runtime fn tr_upper` (`runtime_program_tests.hthr`), compiled as `tr_upper::source` |
| `write-elf` of any nullary `Source`, `<s>_elf_simulates` | `crates/cli/src/native/elf.rs`, `native_compile_elf` | built |
| Data segment sized to the program (1 MiB buffers) | issue `native-data-capacity` | built |

So `tr` already runs as a compiled computation over `Io` with its theorem,
but its `ELoop` was written by hand beside the surface method it models
(`Io::tr_upper`), and the two are tied by probes at one scripted world, not
by a theorem at every world.

The gaps, each a section below:

1. **The reflector does not read a `while` over `Io`** (§2.1), and nothing
   proves the surface loop equal to the `ELoop` meaning (§2.2).
2. **The reflector does not read a call of a span `runtime fn`** as `Lend`
   (§2.3).
3. **No generator publishes the program** (§3): its `Source`, the `Reads`
   theorem, a name `write-elf` takes.
4. **A read lands at its buffer's start** (`CallShape::Reads`,
   `Effect::Reads`), so no program can read all of its input into one
   buffer (§4.1).
5. **A branch whose arms call Linux** (`EIf`) is not modelled (§4.2; built
   since, as `ETm::If`).
6. **No constant bytes** to write: a program cannot print `"valid\n"`
   except by storing it a byte at a time (§4.3).

## 2. The front: reading a surface program

### 2.1 Reading a `while` over `Io` into `ELoop`

The surface `while c { body }` with no measure is, after the parser
(sequencing design §18), one call

```
Iterate::then(init, λ #s => { v̄ = #s; match decide_bit<c>() {
    True => { body; Pointed::ret(Continue(v̄')) },
    False => Pointed::ret(Break(v̄)) } }, λ #b => rest)
```

where `v̄` are the locals the body assigns, `io` among them (a `mut self`
call assigns it), nested as `Mutated(v₁, Mutated(v₂, v₃))`. The body is
straight world threading, which the reflector already reads. So the reading
is:

- the state's locals become the `ELoop` environment (in the order the state
  nests them), `io` removed: it is the world the layer threads, never a
  value;
- `decide_bit<c>()` reflects as the pure `Tm` condition over that
  environment;
- the `True` arm's body reflects as the pass, an `ETm`, by the existing
  chain walk, and the state it continues with gives `rebind` (each
  variable's position in the pass's end context);
- the `False` arm must break with the state unchanged (`Break(v̄)`), and the
  reflector refuses anything else;
- `rest` reflects as the `ELoop` after the loop, with the loop's exit state
  as its environment (`k`'s parameter, projected as the state was).

Several loops in sequence are `Iterate::then` nested in `rest`, so they read
as `While(…, While(…, Done(…)))`, and straight code between them as `Seq`.
That is exactly the program shape `ELoop` already has, chosen in slice 5 to
match the surface's threading.

### 2.2 The bridge: the surface loop is the `ELoop`'s meaning

A loop-free body's pin is `refl`: `ETm::sem` is written so that it unfolds
onto the elaborated body node for node (`echo_reflects`). A loop's is not,
for two reasons, both about shape and not about meaning:

1. **The state.** The surface iterates a nested `Mutated` of the locals with
   `io` inside it; `ELoop::run_while` iterates `Mutated<Io, rt::Env>`, the
   world outside and the values as `rt::Env`'s nested `Pair`s ending in
   `trivial`.
2. **The rotation.** The surface's pass tests the condition and then runs
   the body (`while`); `ELoop`'s tests once outside and then runs body-then-
   test (`if c { do body while c }`, which is what the lowering emits). The
   surface goes round one more time, so the two are equal up to silent
   steps (`Eutt`), not in lockstep.

Both are general facts about iteration, so they are proved **once**, in
`linux_world_co` beside `Io::iterate_rel`:

- **`Io::iterate_rotate`**: for a total test `t` and pass `p`,
  `CoTree::iter` of "test, then pass" from `s` is `Eutt` to "test once, then
  `Io::iterate` of pass-then-test". This is the Elgot iteration's
  dinaturality law at `Partial`, by direct corecursion as `iterate_rel` is.
- **`Io::iterate_encode`**: iterating a step over states `S`, read through
  an encoding `e: S → Mutated<Io, A>` that the step commutes with, is
  iterating the encoded step. With `iterate_rel` this is the case `R(a, c) :=
  e(c) = a`.

The generator then states the per-program pin as those two lemmas applied,
whose remaining premise is that **one pass** of the surface step, read
through the encoding, is the `ELoop` pass: a statement about a straight
body, which converts by `refl` exactly as a loop-free pin does today. No
per-program induction, no per-program corecursion: the coinductive work
lives in the two lemmas (principle 4 of the vision note).

If the pass's pin does not convert (the encoding's projections against
`rt::Env`'s pairs are where it could), the fallback is to make
`rt::Env` at a list of codes reduce to the surface's own nesting. That is
a change to `rt`'s environment type, local to this layer, and the slice
records which it took.

**As built (2026-11-15).** One lemma, not two: `Io::while_agrees`
(`linux_world_while`) takes the surface's test `c` and body `b` as
functions of its state, the lowered loop's test and pass, the readings
`world`/`vals` of a state, and three premises (`WhileAgrees`: same test,
same body, same rest), and proves the surface loop and its rest `Eutt` to
the lowered loop and its rest, by direct corecursion. The two shape
differences are both inside it. The reflector records how it read each
loop (`LoopProof` in `rt_io_reflect_loop`: the state before it, `c` and
`b` as `λ`s over the state it opened the step at, the rest's opened body),
and `io_loop_bridge` (`rt_io_bridge`) writes the proof term: one
`Io::while_agrees_by` a loop, its test and body premises `refl` at a state
of the loop, its rest premise the bridge of the rest (`Eutt::refl` at
`Done`). `rt_io_while_tests` holds it for echo, for two loops in sequence
with parameters no loop threads, and refuses it against a wrong program.
No change to `rt::Env` was needed: `vals` spells each component out of the
state's nested records.

### 2.3 Calls of span functions: `Lend`

A pass that calls a `runtime fn` lent a span, as `tr`'s does
(`raise_span(r.buf, BitVec::ofNat(r.buf.len()), r.result, 0)`), reflects as
`Lend(f, cap, buf, args, body)`:

- the callee is one of the program's runtime fns (the generator collects
  them as it does for pure code, `f::program`, callees first);
- the span argument is a buffer variable of the environment, its length
  argument the buffer's capacity, and the rest words;
- a writer's result (`Mutated<List<u8>, u64>`) binds the bytes it left and
  its word, as a read binds its buffer and count; a reader's answer is its
  word, and the buffer is unchanged;
- the old buffer variable is gone after the call, as after a read, so a
  use of it is refused at the lowering (the control `tr` already has).

The table `ls: List<Lent>` and the `ETm::LentsAgree` premise of
`lower_reads` are discharged from the callee's published `f::runs_over`
(writers) or `f::agrees` (readers), as `tr_lents_agree` does by hand today.
The generator writes that proof; it is the same few lines for every
callee, so it is a lemma over the callee's group, not per program.

**As built (2026-11-15).** The reflector is given the lent functions in
the table's order (`reflects_io_loop_as(…, lends, …)`, `io_loop_bridge(…,
lends, …)`). A call of one is made where a call on Linux, a loop's pass or
the end first needs its answer (`rt_lend_calls` scans their operands,
innermost call first), binding its bytes (`m.after`) and word
(`m.value`) as a `Lend`; its length argument must be
`BitVec::ofNat(buf.len())` of the buffer it is lent, else it is refused.
`Io::tr_upper` reflects to `tr_prog()` exactly (`rt_io_lend_tests`), and
its bridge is written and checked the same way as echo's, the table
`tr_lents` taken by name. A reader (answer only a word) is the generator
round's, with the table.

What it inherits: a program lends a function a **prefix** of its buffers,
so the buffer lent is the program's first (issue `source-buffers-as-views`).
One buffer is enough for every program in §0 and the demo thread's three.

## 3. The program a generator publishes

A `runtime fn` whose first parameter is `io: Io` and whose result is
`Partial(Mutated<Io, u64>)` (§5, D1) is a **program**. The generator (the
same `runtime` generator, a second mode, as the lent mode is) publishes,
beside `f`, one group:

| Member | What it is |
|---|---|
| `f::eloop` | the reflection, an `ELoop` over the program's world and lent table |
| `f::program` | the FunctionIR functions it calls, callees first (as today) |
| `f::lowered` | `f::eloop.lower(…)`, by evaluation `Some` |
| `f::source` | `Source(functions := f::program, buffers := …, words := stmt.word_bound(), main := Then(stmt, Exit(result)))` |
| `f::starts` | `f::source.start([])` is the environment the theorem starts from: every buffer zero (`tr_lend_starts`) |
| `f::reads` | `Io::Reads` of `f::source`'s fuel-free tree, mapped to its exit status, against `λ io => f(io, zeros…)` mapped to its value |

`f::reads` is `ELoop::lower_reads` (proved once) composed with the bridge
(§2.2) and the `Exit` at the end (a `reads_bind` with a leaf). Nothing in it
is written for `f`.

**`write-elf` takes it by its path.** Today `write-elf <file> <source>`
takes a plain identifier (`symbol_ok`); it learns `f::source`, and the
certificate names its members after it (`f::source_elf_simulates`, …).
The certificate then has every link: the file simulates the `Source`
(`elf_simulates`), the `Source`'s fuelled program and its fuel-free tree
refine each other (`Source::tree_co_refines`), and the tree reads as `f`
(`f::reads`). A last theorem, `Source::elf_reads` in `native_compile_elf`,
states the composition once, so a program's certificate can cite it
directly: every trace of the process is a trace the world-threading meaning
`f` allows.

**The customers this round moves** (effects design §6 item 5): `tr` written
once, as the surface `Io::tr_upper`, a `runtime fn`, compiled from its
reflection; its hand-written `ELoop` and its builder version go. Then the
demo thread's programs.

**As built (2026-11-16).** `lib/native/runtime/runtime_program.hthr`; a
module of programs imports it in place of `runtime` (its `runtime` is
`runtime`'s with the program mode in front, and the two names would
clash). What differs from the table above:

- The group is `f::eloop`, `f::lents` (the table), `f::bridge`,
  `f::source` and `f::reads`. A group's members cannot name each other
  (a generator builds every term before it publishes), so the lowering,
  the program and the start are not members: `f::source` is
  `Program::source(eloop, lents, g, functions, caps)`, and the statements
  are `Program::stmt`/`Program::result` of the same arguments.
- A buffer parameter is `buf: ByteBuffer(n)` (a list of bytes, of which
  the process starts with `n` zeroes); `[u8; N]` waits on I/O over
  vectors. The reflector reads a type alias as what it stands for.
- The world is plain (`ETm::plain_world()`): a lent function's callees
  are its own program's business, and a table entry names the program
  function it is (`Lent::entry`), not `w.sigs.len() + f`. A pure term
  that calls a function is refused for now.
- The functions a program lends its buffer to are found in its body
  (`program_lends_in`: a callee with a generated `runs_over`); one for
  now, since programs of two are not linked into one. Its agreement is
  `Lent::agrees_span` from its `runs_over` (`Words::All` turns the
  curried theorem into one over the word list).
- The exit: an exited flow reads back as its status, and
  `Stmt::exit_eutt`/`Stmt::exit_reads` (`rt_io_program`) make the
  lowering's theorem one about `Then(stmt, Exit(result))`, so `f::reads`
  is `Stmt::exit_reads(…, Program::reads(…))` with the bridge at the
  zeroed buffers (`Program::reads` is `lower_reads` then `reads_back`).
- `write-elf <file> [<source>]` takes a path (`tr_upper::source`), and
  `main::source` when none is named; the certificate's names take the
  path with `::` as `_` (`tr_upper_source_elf_…`). `Source::elf_reads`
  is not written yet: the certificate and `f::reads` meet at
  `f::source`'s tree.
- `tr`: `runtime fn tr_upper(mut io: Io, buf: ByteBuffer(256))` is the
  gate's tr. The hand `ELoop` in `rt_io_lend_tests` stays as the
  reflector's pin and the lowering's probes. The builder tr stayed until a
  program could exit 1 on a failed write; round 5 (§4.2) removed it.

**As built (round 4, 2026-11-16): a whole input, then a verdict.** The
validator's shape is a loop that reads standard input into one buffer at a
growing offset (`filled`), stopping when a read brings nothing or fails,
then one lent call after the loop whose word is the exit status
(`ascii_check` in `runtime_program_tests`, held to a reference by
`native_tools`; the UTF-8 validator's `main` in `examples/utf8` is the
same program over `utf8_valid_from`).

- A lent function must pass its span's length on as it is, so the length
  the program lends is the buffer's capacity and the count of bytes read
  is one more word: the verdict function is
  `f(span, length, filled, failed)` and validates the first `filled` bytes
  (`utf8_valid_from(span, length, 0, filled)`); its theorem rests on a
  window lemma over `s.take(filled)` (examples/utf8 `valid_prefix`).
- A loop threading three locals or more reads a field of a field of its
  state (`z.value.value.after`); `rt_settle_named` settles those a level at
  a time.
- `write-elf`'s certificate states `Prog::links` a check at a time
  (`Prog::links_of`: evaluable a function per declaration, as
  `compile-x86`'s is, then placeless, rowed, and the emitted functions), so
  a program that links a validator's eight functions fits the kernel's
  per-declaration fuel.
- A module of programs imports `runtime_program` and what its own text
  spells, nothing of the generators' (since 2026-11-16): `bitvec` (`u8`,
  `u64`), `itree` (a `while`'s `Iterate`), `coitree` (`Partial`),
  `linux_world` (`Io`), `rt` (`byte_within`), `rt_io` (`read_into`). The
  generators name what they state by key, `name_of(X)` where they can see
  `X` and `"module::X"` otherwise, and a generated instance cites its class
  by key (`runtime::Compile`, `runtime_file::CompileSpan`), so each needs
  its module only in the program's import closure; `runtime_program`
  imports `runtime_file`, so span functions can sit beside the program.
  Before, a generated name resolved where the program was, and a program
  imported the generators' whole vocabulary (about forty modules).

## 4. Three nodes a real program needs

### 4.1 A read at an offset

`read(fd, buf + at, len)`. Without it a program reads at most one buffer's
worth at a time from the start, so it cannot hold its whole input (a
validator, a sort, a search over the input all can). The write side already
has its offset (`Writes(fd, buf, from, len, result)`). The change:

- `CallShape::Reads` gains `at` (a word, after the buffer, as `Writes`'s `from` is), and the read lands its bytes at
  `at` (`fill_at`, as `span` is `write`'s), refusing nothing: Linux is
  asked for at most `buffer length − at` bytes, as it is asked for at most
  the buffer's length today;
- the x86 lowering adds the word to the buffer's address; the compiler's
  proof of the read's case moves from `fill` to `fill_at`;
- `Effect::Reads` and `Io::read_into` gain the same operand, and the
  builder's `read` passes 0.

This is a compiler change (in the native layer, not the kernel), every
existing program passing `at = 0`, and its byte output for them is the
same plus one `ADD` or none (an immediate 0 is folded).

### 4.2 A branch whose arms call Linux: `ETm::If` (built)

A pass that writes only sometimes (`grep`, an error message on a failed
read), or a loop that stops on a failed write (`tr_upper`), needs a branch
over `ETm`. A statement `if` elaborates (`imperative.rs`'s `join`) to one
record of the locals its arms assign, the world among them, in the order
they are first assigned: `#stage = match decide_bit(c) { True =>
Mutated(io₁, Mutated(k₁, s₁)), False => … }`, every later read a field of
it (`#stage.value.after`); one local alone is the local.

**The node** (`lib/native/runtime/rt_io.hthr`):
`If(cond: Tm, yes: ETm, no: ETm, parts: List<Part>, body: ETm)`, a `Part`
being `PWorld` or `PVar(t, y, n)`, a local of code `t` at index `y` at the
end of the `yes` arm and `n` at the end of the `no` arm. Each arm runs to
its end from the state before the `if`; its own result is not read. The
meaning builds the same record, `Part::branch` (one `match` on the test's
truth) of `Part::state` of each arm's end, and runs `body` with each
`PVar` a new variable (`Part::push`, in the record's order) and the world
`Part::world` of it. That is the surface's own shape, so the pin
`meaning = f` is `refl` at a neutral test: no commuting conversion and no
lemma was needed, against what this section first proposed. The
variables before the `if` are untouched; the locals it assigns are new.

**The lowering** (`rt_io_lower.hthr`, `ETm::lower_if`): the test into a
flag; `Branch` on it, each arm its statements and then the moves
(`Loc::moves`, the loop's) that bring each `PVar` word to one fresh word
past both arms' (`ETm::join_lower`); a byte buffer stays where both arms
leave it, else it is gone; a variable from before the `if` keeps its place
where both arms leave it there (`Loc::meet`). It is proved in
`ETm::lower_sound` (`ETm::lower_if_sound`): each arm by the induction
hypothesis (`ETm::arm_sound`), the moves by `Loc::moves_sound`, and the
join's places by `ETm::join_sound`. An `if` that does not assign the world
lowers only when neither arm calls (`ETm::silent`).

**The reflector** (`rt_io_reflect`, `rt_reflect`): the host's `Arms`
answers a field read of a `match`'s record as that `match`, its arms
whole, with the fields read (`MatchInfo::path`). A world that is such a
read is on the world chain after the calls both arms' worlds start with
(`rt_world_calls`), and the walk makes the `if` there (`rt_if_make`); a
read of a local of an `if` that does not assign the world is made when a
term first needs it, as a lent call is (`rt_lend_find`). The arms are read
from the state before the `if`, under one local (`rt_bool_arms`), and each
local after it is the variable `IfRes` names. The calls before an `if` are
the run both arms start with, so an `if` whose two arms begin with the same
call reads that call as before it, and the pin then refuses the program.
`if h:` that assigns locals is refused for now.

### 4.3 Constant bytes

A `Source`'s buffer can start with bytes (`yes`'s line, `Buffer`'s
initial contents, emitted into the data segment as `emission::Inits`).
What is missing is the surface: a program writing `"valid\n"`. Two shapes,
§5 D3.

**The surface (built, 2026-11-16).** `b"valid\n"` is the name `b` with a
string literal right after it, no space between (`Parser::byte_string`; `b`
alone or `b "x"` is what it was). Its bytes are the string's characters,
each ASCII, since a non-ASCII character is refused rather than read as its
UTF-8 encoding; the escapes are a string's (`\n`, `\t`, `\r`, `\\`, `\'`,
`\"`, `\0`, `\u{…}` up to `7F`), and a byte above `0x7F` has no spelling
yet (`issues/byte-string-hex-escape.md`). It elaborates (`Literals::elab_byte_string_*`)
to the collection literal of its numerals at `[u8; n]`, or at
`List<u8>` where a list is expected (a `ByteBuffer(n)` is one), so it is
exactly the term `[118, 97, …]` would be, with nothing new in the kernel;
`lib/_tests/std/bitvec/byte_string_tests.hthr` pins it.

**The native half (built, 2026-11-16): a byte string is one more buffer
parameter.** D2's move, applied by the reflector: before reading a program,
`rt_const_scan` finds every closed list of byte literals in its body (each
once, by its bytes, in the order the walk meets them), and the reading
takes each as a parameter after the function's own (`Known::consts`, its
level; `rt_const_bytes` reads a `Cons` spine at a byte buffer as that
parameter, where it used to refuse it as a `Cons` onto a buffer). So
nothing below the reflector is new: the lowering places the parameter in
a buffer like any other (`Program::locs`), and its theorem is unchanged.
The generator gives the `Source` one buffer per string after the
parameters' (`Program::all_buffers`: `Program::constant(bs)`, of its own
length, `initial := bs`), states `f::reads` at no argument for the strings,
and proves the reading's environment holds each, `rt_bytes([…])` of its
bytes, by `refl` at `Source::start` (`Program::held_cons`), as it does for
the zeroed buffers; the bridge's environment holds the same terms
(`bridge_consts`), which convert with the literal in the body. A string the
program reads into is then a buffer the read overwrites, as a parameter
is, and the lowering forgets it there, so "never written" needs no check
of its own. `ascii_say` in `runtime_program_tests` says its verdict with
two strings by an `if`, and `native_tools.rs` holds its output.

## 5. Decisions (Minus, 2026-11-15)

**D1. What a program is.** Any `runtime fn` whose first parameter is the
world, written `mut io: Io` (a `mut` parameter is threaded as a `let mut`
is, so no `let mut io = io;`), and whose result is
`Partial(Mutated<Io, u64>)` compiles as a program; the `u64` is its exit
status. A function named `main` is the entry point: `write-elf <file> -o
<out>` builds `main`, and `write-elf <file> f::source -o <out>` any other.
So `main` is special only as the default, and every effectful function is
compiled the same way (a program's helper over `Io` is a program too, which
is what `rt-effectful-callees` will call).

**D2. Memory: the meaning and the machine are separate questions.** Two
things were run together in the first draft:

- *The meaning.* A buffer is a value, `List<u8>` (or `[u8; N]`), in the
  program's world-threading meaning. Nothing about memory appears there:
  the program reads into a list, lends it to a function, writes a span of
  it. This is what a theorem about `main` talks about.
- *The machine.* Where those bytes live: a zero-filled range of the data
  segment the `Source` declares (`Buffer(capacity, initial)`), which the
  lowering places (`Loc::InBuffer`). That is operational, like a register
  placement (vision note §2.5).

The surface question is only how a program says it needs a buffer and
what it starts as. Both spellings are allowed, and they give the same
theorem:

- a local, `let mut input: [u8; N] = [0; N];` (or a byte literal, D3),
  which reflects as a static buffer of the `Source` with those initial
  bytes;
- a parameter after `io`, `input: [u8; N]`, which is a buffer the caller
  (the process start) supplies zeroed.

The generic theorem that makes them one: a program with a buffer local
initialised to `v` is the program with that local abstracted as a
parameter, applied to `v` (`f_local(io) = f_param(io, v)`). The
generator always states `main::reads` in the parameter form at every
initial content and instantiates it at the declared `v`, so the kernel
never converts a term holding `N` literal zeros: the zeros appear only as
the argument of a statement already proved for every list. The same
abstraction is what a user wants for "pull this constant out as an
argument" in their own proofs; it is a lemma about the reflected
`ELoop` (substituting a variable's initial value), proved once, not
per program.

**As built (2026-11-16): a zeroed local is read like a byte string.** A
local `let mut buf: List<u8> = List::replicate(0, n);` at a numeral `n`
is one more parameter of the reading after the function's own, as a byte
string is (`rt_const_scan` records it as `ConstInit::Zeros(n)`, one buffer
per local even where two start alike, in the order the body makes them).
The `Source` holds it as `Program::zeroed(n)`, a zeroed buffer of that
capacity, and `f::reads` is stated with no argument for it, its
environment holding `List::replicate(zero_byte(), n)` by `refl` at
`Source::start`. So the general abstraction lemma above was not needed:
the reading never holds the local's value, only a variable for it, and
the parameter form and the local form read alike
(`ascii_local::eloop = ascii_check::eloop` by `refl`,
`lib/_tests/native/runtime/runtime_program_tests.hthr`). A local that
starts as other bytes is refused, naming a byte string as the spelling:
the data segment starts a program's own buffer zeroed.
`examples/utf8/utf8check.hthr`'s `main` makes its buffer this way.

**D3. Constant bytes.** Agreed: byte-string literals `b"valid\n"` of
type `[u8; 6]`; a literal reaching a write is a constant buffer of the
`Source` (initial bytes in the data segment, never written). After the
demos, which report through the exit status.

**Not a decision, recorded:** §4.1 changes `Io::read_into`'s signature
(adds `at`). It is the word-level call that effectful runtime code makes,
not user surface; `Io::read` (the world-level call specs use) is
unchanged.

## 6. Rounds

In order, each its own PR; (P) marks work independent of the rounds before
it, so it can run in another thread at the same time.

1. **Reflect loops** (§2.1, §2.2). The two iteration lemmas, the
   reflector's `while`, its pins. Done when `Io::echo_all` and
   `Io::tr_upper` reflect to the `ELoop`s their tests write by hand, with
   `reflects_io_as`, and the bridge theorem holds of each at every world.
   Includes `Lend` reflection (§2.3), since `tr` needs it.
2. **The program generator and `write-elf` by path** (§3). Done when
   `Io::tr_upper` is a `runtime fn`, `write-elf … tr_upper::source` builds
   it, the gate holds it to GNU tr, and the hand-written `ELoop` and the
   builder `tr`s go.
3. (P) **Reads at an offset** (§4.1). Done when a program reads its whole
   input into one buffer in a loop and the existing GNU gates are
   unchanged.
4. **The demos**: UTF-8 validator first (demo thread), each one program and
   one binary.
5. (P) **`EIf`** (§4.2, built: `tr_upper` exits 1 on a failed write, its
   gate holds it to GNU tr on `/dev/full`, and the builder `tr`s are
   gone), then D3's literals (§4.3), then the rest of
   effects design §6 item 5 (`cat FILE…`, `wc`, `head -n` rewritten, the
   builder deleted).
6. **After the UTF-8 program (2026-11-16, Minus's order).** Generated
   declarations resolve outside the program's own imports (§3, built);
   then D2's local buffers (§5, built). Filed for
   later: printing (`issues/io-program-prints-output.md`), the sort and binary-search
   demos as programs (`issues/io-program-demo-mains.md`), and the
   whole-program theorem over the read loop and exit
   (`issues/io-program-whole-theorem.md`).
