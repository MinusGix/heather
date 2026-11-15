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
| `tr` as one `ELoop` term, through `write-elf`, held to GNU tr | `rt_io_lend_tests.hthr`, `native_tools.rs` | built, written by hand as an `ELoop` |
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
5. **A branch whose arms call Linux** (`EIf`) is not modelled (§4.2).
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

### 4.2 A branch whose arms call Linux: `EIf`

A pass that writes only sometimes (`grep`, an error message on a failed
read) needs `EIf(c, a, b)` over `ETm`. Design §8.4 names the obstacle: a
statement `if` with calls in its arms joins per variable (`imperative.rs`),
so the elaborated body projects `io` and each other local out of the
branch's tuple, and an `EIf` meaning that branches over the whole
`Mutated` needs a commuting conversion to agree by `refl`. Proposed: the
reflector reads the per-variable join, and the pin goes through one
equation proved once (`if c then (a.1, a.2) else (b.1, b.2)` is
`(if c then a else b).1, …`, which is `refl` per projection on a neutral
`c` only when the kernel has the commuting conversion; otherwise it is a
`Bool` case split, one lemma). The lowering is a `Branch` on the flag,
both arms ending with each variable at the same place, as a loop's pass
does with its moves back.

None of the programs in §0 or the demo thread's three needs it (each
computes its answer in pure code and writes once), so it comes after them.

### 4.3 Constant bytes

A `Source`'s buffer can start with bytes (`yes`'s line, `Buffer`'s
initial contents, emitted into the data segment as `emission::Inits`).
What is missing is the surface: a program writing `"valid\n"`. Two shapes,
§5 D3.

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
5. (P) **`EIf`** (§4.2), then D3's literals (§4.3), then the rest of
   effects design §6 item 5 (`cat FILE…`, `wc`, `head -n` rewritten, the
   builder deleted).
