# From cat to real tools: what blocks the native compiler, and the order to fix it

Status: **plan, 2026-10-26; nothing built.** Written at Minus's request to
stop waffling and get to native programs that run as general-purpose (if
limited) Linux tools. It is a plan, not a survey: every blocker below was hit
by building a program on master (`aee4a09`) with `heather write-elf`, and
each round in §6 is filed as an issue under the milestone `hih-tools`
(`docs/roadmap.md`).

The constraint from `docs/native-program-logic-design.md` holds throughout:
the compiler is proved once (`native_compile_correct`). No round below adds a
per-program proof. A tool's correctness is its source's tree, and a spec proof
about that tree (`Program::Implements`) is optional extra, as `cat_implements`
is for cat.

---

## 0. Verdict

**What runs today.** Any `Source` (`lib/native/native_source.hthr`) whose
leaves are small dataflow regions, whose calls are `read` and `write`, and
whose data fits one 4 KiB page, compiles through `write-elf` into a static
ELF that Linux runs. I built and ran four on master besides cat: `exit 3`, cat
to stderr, `head -c 10`, and cat with its pass inlined twice. Each took one
`write-elf` and no proof. So the pipeline is real. The programs it can express
are not: **no program can look at a byte**. A computation sees only the
64 words of its environment. Buffers are touched only by Linux, so the only
thing a program can do with input is copy it whole or count it. That rules
out `tr`, `wc`, `grep`, `head -n` and everything else that looks at its
data.

**The five blockers, in the order to remove them** (ranked by how many tools
of §2's target set each one stands in front of, then by what the next round
needs):

1. **Bytes.** Leaves cannot load or store a buffer byte, and a program cannot
   start with constant bytes (no string literals). Blocks 11 of 14 tools:
   every one that does not already work.
2. **Compile capacity.** Building a program with three times cat's code
   peaks near the suite's whole 6 GiB rail, and at six times it exhausts the
   cloud box's memory. Peak memory grows about as the square of code size.
   Real tools will be many times cat. Blocks every tool past toy size.
3. **Writing programs.** A `Source` is a hand-written AST over numbered words,
   and a leaf holds at most 14 values (inputs plus one per node). A real tool
   cannot be written this way at any reasonable cost. Blocks every tool past
   toy size.
4. **The command line and files.** No argv, and `open`/`close` are refused by
   the compiler. Blocks 9 of 14 tools.
5. **Room and numbers.** All data shares one 4 KiB page, and there is no
   decimal output or input (no multiply, divide or shift in the ISA model).
   Blocks 6 of 14 tools.

**What to start, in order** (§6 has each round's scope): `native-source-bytes`
and `native-compile-capacity` now, in parallel, with
`native-elf-every-program` beside them as a small round. Then
`native-compile-wider-leaves` and `native-source-builder`. Then argv, `open`,
data capacity and decimal I/O, which are four independent rounds. Last,
`native-tools-suite`, which builds a dozen tools, tests them against GNU, and
is where the milestone is done.

**Deferred on purpose** (§7): register-resident words, procedures that make
calls, heap allocation through `mmap`/`brk`, and the uniqueness-typed
surface. None of them stands between us and a dozen working tools.

---

## 1. What I ran

Every probe is a nullary `Source` in one file, built with
`heather write-elf <file> <name> -o <out>` over a warm image store and run on
real inputs (2026-10-26, cloud box). Costs are stated as shapes, per
`CLAUDE.md`.

| program | what it is | result |
|---|---|---|
| `cat_source` | master's cat, 1024-byte buffer | builds and runs. A cold image store costs a few minutes, nearly all of it building the library. |
| `exit3` | `Const` then `Exit` | builds and runs, exits 3 |
| `cat_err` | cat with word 1 set to 2 | builds and runs, writes to stderr |
| `head10` | `head -c 10`: cat whose read length is a countdown word | builds and runs: 10 bytes from any input, exits 0 |
| `opens` | one `Invoke(Opens(…))` | refused, with no reason given (`did not compile, or its items' lengths did not read back`) |
| `wide_leaf` | one leaf of 15 `Const`s | refused, with no reason given. The leaf allocator gives each node its own register from a pool of 14. |
| `big_cat` | `cat(2048)`: buffer, scratch and words past the 4 KiB page | **builds and runs**, though `native_compile_correct` does not apply to it (§3.6) |
| `cat_x2` | cat's pass inlined twice (≈1.7× cat's bytes) | builds and runs. Peak memory is about a third of the suite's 6 GiB rail. |
| `cat_x4` | inlined four times (≈3× cat's bytes) | **aborts** under the 8 GiB rail `CLAUDE.md` gives a direct run (`memory allocation … failed`, inside `evaluate_numbers` on write-elf's fork). With the rail raised it builds, peaking at about the suite's whole rail, with roughly twice `cat_x2`'s time. |
| `cat_x8` | inlined eight times (≈6× cat's bytes) | **killed by the box's OOM killer** with the rail raised past the box's memory, after about as long again as `cat_x4` |

Writing `head -c` also hit two frictions. Neither is a blocker, but both slow
every new program down:

- A program file must import the certificate's modules itself
  (`native_compile`, `native_compile_correct`, `linux_x86_64_image`, the
  x86 modules). Otherwise `write-elf` fails with `unknown module
  native_compile: it is not in this run's import closure`.
- A leaf must not write a word it reads (`leaf_checks`'s `ports_absent`), so
  `n := n - r` takes two leaves and a temporary.

---

## 2. The target set

Fourteen small tools, chosen because together they exercise everything a
general-purpose command-line program does: GNU-compatible behaviour under
`LC_ALL=C`, limited where noted.

| tool | needs |
|---|---|
| `true` / `false` | exit status. **Works today.** |
| `cat` (stdin) | read, write. **Works today.** |
| `head -c N` (N fixed at build) | read, write, counting. **Works today.** |
| `yes [STR]` | constant bytes, argv for STR |
| `echo ARGS` | argv, constant bytes (space, newline), byte copy |
| `basename` / `dirname` | argv, byte loads |
| `tr SET1 SET2` | byte load/store (sets fixed at build first, from argv later) |
| `rev` | byte load/store, a line longer than one read |
| `cat FILE…` | argv, open/close, stderr diagnostics |
| `head -n N [FILE]` | byte loads, decimal parse of N, argv, open |
| `wc [-clw] [FILE…]` | byte loads, decimal output, argv, open |
| `cmp FILE1 FILE2` | byte loads, two open files, decimal output |
| `grep -F PAT [FILE]` | byte loads, argv, open, line buffer across reads |
| `sort` (lines of a small input) | byte load/store, input held whole (room), argv/open |

`uniq`, `tac`, `od -c` and `tail -c` need nothing beyond the union of the
above, and come free with the last round.

---

## 3. The blockers

Each blocker says what it is, the evidence, which tools it blocks, and the
fix's shape. §4 counts.

### 3.1 Bytes: no load, no store, no literal

`Stmt::Compute` runs a FunctionIR region over `Env::valuation()`, the words
only (`native_source.hthr`). FunctionIR's `Node` has constants,
`Add`/`Sub`, the bitwise ops, shifts and three comparisons, all on word ports
(`function_ir.hthr:41`). Nothing reads or writes `env.buffers`. Only
`CallShape::answer` writes a buffer, and only `Writes` reads one. So:

- no program can test a byte (`tr`, `wc`, `grep`, `head -n`, `basename`…);
- no program can put a byte it chose into a buffer (`yes`, `echo`'s newline,
  any diagnostic message, any number it prints), since `Source::start` zeroes
  every buffer.

The machine side is already there. The compiler copies a read's bytes with
`LoadByte`/`StoreByte` (`Prog::copy_in`), and `native_compile_calls` proves
that copy byte by byte (`Target::copy_byte`, `goes_copy_loop`). The fix is
the representation, not the instructions.

**Fix (recommended).** Buffers become state edges in FunctionIR, as the
design already decided (`native-effect-source-design.md` §6, Minus's input in
`native-program-logic-design.md` §10 item 6). `Load(out, buf, index)` and
`Store(buf, index, value)` nodes act on a region's buffers as well as its
words. `eval` threads the environment's buffers, and `Env::compute` passes
them in and takes them back. An out-of-range index is clamped as the
source's calls already clamp, so a load reads zero and a store does nothing.
No `Faulted` outcome is needed yet.

What changes from `issues/function-ir-buffer-state-edges.md`: under S3.2's
invariant every buffer already lives in the region (`Target::Placed`), so the
statement compiler can lower a load or store with the facts it already has.
That needs **no** memory footprint on a `Proved` contract
(`wp-proved-memory-contracts`) and no change to S4's register lowering, which
only has to refuse the new nodes. A leaf with byte nodes is compiled split at
each byte node: each pure stretch goes through S4 as today, its results are
settled to their slots, and the byte node runs as load-index, load-or-store,
settle. Keeping values in registers across a byte node is later work, in
`native-compiled-code-shape`, and changes no theorem. So the blocked-by on
`wp-proved-memory-contracts` goes away.

**Constant bytes** come in the same round. `Source.buffers` becomes a list of
`Buffer(capacity, initial: List<BitVec(8)>)`. `Source::start` fills each
buffer from its initial bytes. The compiler stores them at entry, a word at a
time, with the `WordStore` rule it already has. The image does not change.

**Why not statement-level `Peek`/`Poke`?** They would be a smaller round. But
they put a pure byte map (the body of `tr`) in the layer's general loop,
which is partial, when L3 says a bounded pure loop belongs in FunctionIR
(`native-effect-source-design.md` §5.4). They would also be a construct
removed again once state edges land, which is the cruft Minus asked us not to
build. State edges compiled in memory first are the decided design reached
by its cheapest proof.

### 3.2 Compile capacity

`write-elf` evaluates `Source::compile` twice on an untrusted fork to read
the program back (`evaluate_numbers` over `_numbers` and `_lens`,
`crates/cli/src/native/elf.rs`). The kernel then checks the emission
equation in one conversion (`<s>_elf_emitted`, by `refl`). Peak memory grows
faster than the code, about as its square: from `cat_x2` to `cat_x4` the
code is under twice as large and the peak about three times as high, near
the suite's whole 6 GiB rail, and `cat_x8` (twice `cat_x4` again) runs out of
the box's memory. The abort is in `evaluate_numbers`, whose `ValueArena`
keeps every value of the read until it returns. The kernel's own conversion
may also grow superlinearly, since its value cache keeps every value of a
query. The probe did not separate the two. The time grows about linearly.

The tools of §2 with flags, files and formatting will be many times cat's
code (an estimate: cat is one read loop and one write loop, and `wc` as a
command is option parsing, a loop over operands, the count step and a
formatter). The profile's file limit is
64 KiB (`MAX_FILE`, a 16-bit size field in `io_elf_header`). So capacity is
the second wall, right behind bytes, and the builder (§3.3) will hit it on
its first real program.

**Fix.** One round, with measurement as its first half:

- Attribute the peak: the fork's read-back against the kernel's emission
  check, with `--timings` added to `write-elf` (it is refused as an unknown
  option today).
- Read the program back in pieces, the way the bytes are already checked:
  evaluate the compile once, name its result, and read stretches, so the
  arena holds one piece at a time.
- If the kernel's single `refl` is the superlinear part, state the emission
  equation a statement at a time. `Stmt::emit` is a fold over `Then`, so a
  program's code is the concatenation of its statements' code at known label
  counters. Each statement's equation is then its own declaration.
- Done when a program at the file limit (64 KiB of code) builds under the
  suite's rail, and the shape (code size against peak and time) is recorded
  in `perf/`.

**Status.** Done (`issues/native-compile-capacity.md`). The read-back was
the peak, and it now reads one part of the statement tree at a time; the
emission is stated a part at a time and joined by three lemmas proved once;
and the layout and bytes are stated by a table of the program's labels,
checked in one pass and proved once to give `laid_out`
(`issues/native-compile-linear-layout.md`), so build time and memory grow
linearly with the code and a program near the file limit builds under the
suite's rail. Its constants are `issues/write-elf-build-constants.md`.

### 3.3 Writing programs

A `Source` today is written as cat is (`lib/native/native_cat.hthr`):
word ids are numerals with their meaning in a comment, a leaf is a list of
`Node` constructors, and `ops([...])` wraps them. Leaf limits leak into the
program. At most 14 values fit a leaf (`register_pool`, `leaf_inputs`,
`leaf_outputs`), and a leaf may not write a word it reads. Control flow is
`Then`/`Branch`/`Repeat` on one-bit words that the program sets itself. `tr`
written this way would be a page of numbered nodes. `wc` with flags would be
several pages, and wrong.

There is no front end for effectful programs. The decided surface is
uniqueness threading that denotes trees (`effects-direction`, design §10 item
5). That is a language design round, and it should not stand between us and
running tools.

**Fix: a builder, in Heather, that the surface will target later.** A small
library (`lib/native/native_build.hthr`) of a structured program type: named
words and buffers, expressions, `let`, `if`, `while`, `for` over a buffer's
bytes, `read`/`write`/`exit`, and procedures inlined at build. A Heather
function lowers it to a `Source`. It allocates word ids, splits expressions
into leaves that fit the register pool, adds temporaries for in-place
updates, and turns `if`/`while` into the bit words that `Branch`/`Repeat`
test. It needs no proof. A tool's meaning is the `Source` it lowers to,
whose tree is what `native_compile_correct` speaks of, and a spec proof
about a tool is about that tree. The uniqueness surface, when it comes,
elaborates into this same builder (or straight into `Source`). So the
builder is that surface's back half, not a detour.

Two pieces make it pleasant:

- **Pure helpers as ordinary Heather functions.** `compile-x86`'s reflector
  (`crates/elab/src/function_ir_source.rs`) already turns a Heather word
  function, with its loops and measure recursion, into FunctionIR. The
  builder lets a leaf call such a function, inlined as its reflected region,
  with the reflector's certificate stating that the region evaluates to the
  function. Inlined regions with conditionals or loops need §3.4.
- `write-elf` evaluates the builder's lowering on its fork, states the
  `Source` literal it gets as a definition (`<s>_lowered() = literal`, by
  `refl`, one cheap declaration), and compiles that literal. The builder's
  evaluation then never adds to the emission check's cost.

**Status.** Done (`issues/native-source-builder.md`), except reflected
helpers (`issues/native-build-reflected-helpers.md`): a helper is a Heather
function over the builder's values for now. `lib/native/native_build.hthr`
binds words and buffers with Heather lambdas and cuts its nodes into leaves
as the compiler takes them (`List::takes`): S4's register leaves where they
fit, round 4's node-at-a-time leaves for byte nodes and in-place updates. cat, tr, yes, `head -c` and `wc -l` are written with it
(`lib/native/native_tools.hthr`). `write-elf` states every source it reads
back as a literal, so the lowering is evaluated once.

### 3.4 Leaves: only small dataflow

`Stmt::emit` compiles `Compute(Dataflow(...))` and refuses `Sequence`,
`Compose`, `Conditional`, `Call` and `Loop` regions, and any dataflow region
with more values than registers (`issues/native-compile-wider-leaves.md`).
The bounded FunctionIR loop, which L3 made the home of pure loops, therefore
cannot appear in a native program at all. Every loop must be the layer's
`Repeat`.

**Fix (re-scoping `native-compile-wider-leaves`).** Compile every region
form **memory-resident**, the way S3.2 compiles statements: each node loads
its operands from their slots, computes in fixed registers, and stores its
result. A `Conditional` is a branch over two such sequences. A `Loop` is a
counted loop whose state words live in their slots. The proof is per
construct, like `Stmt::emit_runs`. There is no register allocation in it, so
there is no register-pool limit. S4's `Region::lower` stays as the better
lowering for a dataflow leaf that fits the pool, and the compiler picks it
when it applies. This is a two-tier compiler (a plain lowering proved once,
plus an allocating one proved once), not a stopgap, and it is what makes
reflected helpers (§3.3) and bounded byte loops (§3.1) usable. `Call`
regions stay refused here, because the builder inlines.

**Status.** Leaves done, 2026-10-27 (`issues/native-compile-wider-leaves.md`,
`lib/native/native_compile_nodes.hthr`). A dataflow leaf S4 does not take
whole compiles a node at a time when every node works at width 64: each
node loads its operands from their slots and stores its result before the
next runs, a pure node through S4 as a region of its own (its output
renamed, so it may read its own word) and a byte node by its own code. So
a leaf has no length limit, mixes byte nodes with arithmetic, and reads
words it writes. `native_compile_correct` covers it through one lemma: the
leaf settles as its nodes do one at a time (`Env::steps_settle`). The
`Sequence`, `Compose`, `Conditional` and `Loop` regions are still refused.

### 3.5 The command line, files, and diagnostics

- **argv.** The machine side states the psABI layout (`ArgvAt`,
  `linux_x86_64_io.hthr`), but the process image maps no stack
  (`issues/io-image-process-stack.md`), the entry state names no RSP, and a
  `Source` has no arguments: its tree is fixed. **Fix:** `Source::denote`
  takes `args: List<List<BitVec(8)>>`, and `Env` starts with `argc` in a
  word. A statement `Arg(k, buf, len)` copies argument `k` into a buffer,
  clamped to its capacity, with its length (or −1 past `argc`) in a word. The
  compiler saves RSP at entry and copies with the read-back loop it already
  has. The proof meets `ArgvAt` from `io-image-process-stack`, which this
  round finishes.
- **open/close.** `Prog::call` refuses `Opens`, `Closes` and both stats
  (`issues/native-compile-other-calls.md`). The machine rules exist
  (`OpenRequest`, `close_rax`). `open` needs its path NUL-terminated. The
  compiler copies path bytes and a NUL into scratch, so the source's buffers
  stay as they were. Stat can wait: no §2 tool needs it if `wc`'s column
  width is pinned to the cases that need no stat (§7).
- **Diagnostics** are a `write` to fd 2 from a buffer with constant bytes,
  so they come from §3.1 and need nothing of their own.

**Status.** argv done, 2026-10-27 (`issues/native-source-argv.md`):
`Source::denote(args)`, `Stmt::Arg` and its compiled copy loop
(`native_compile_args`), with `echo` and `yes STR` built by `write-elf`
against GNU. Two departures from the fix above. No word holds `argc`: `Arg`
past the last argument sets its length to −1, which is how a program
counts them, so the environment's words all still start at zero. And the
image maps no stack region yet: the ELF theorem takes the entry memory as
the loaded file below `0x412000` and `ArgvAt` above it as hypotheses,
which is what Linux hands a process, and no compiled code uses a stack. The stack region proper stays with `io-image-process-stack`, for a
compiled callee that spills.

**Status.** open/close done, 2026-10-28
(`issues/native-compile-other-calls.md`): `Prog::call` compiles `Opens` and
`Closes` (`native_compile_opens`), and `cat FILE…` is built by `write-elf`
and run beside GNU's, diagnostics and exit status included. The path an
`Opens` names is its buffer's bytes up to its length *or its first NUL*
(`List::before_nul`), since Linux reads a C string; the compiled copy loop
stops at either and stores the NUL after them in scratch, which is one byte
longer than the largest buffer for it. Stat is still refused
(`issues/native-compile-stat.md`). cat's messages are a table scanned at
run time, so the code that writes a diagnostic exists once; it holds the
messages of twenty-six errnos in glibc's spelling (those an open, read or
write can return, and EPERM), and says "Unknown error" past them where GNU
names the errno or adds its number (decimal output is round 9). Round 7
first held seven, because two of `write-elf`'s statements were one kernel
`refl` each under fixed fuel: the builder's lowering of the whole tool,
and the entry that stores a buffer's initial bytes one instruction each.
Both are now stated by parts (`issues/native-tool-certificate-budget.md`):
the lowering is a left fold (`List::pack`) whose parts are joined by a
lemma per `Act` constructor (`lib/native/native_build_parts.hthr`), and
the entry's bytes go 32 at a time; the allocation check is stated over the
emission's parts too. The few statements still linear in the tool are
cheap per unit (the issue's log names them). The round also made
`write-elf`'s byte read linear (`asm_code_ending_onto`): it nested its
appends to the left, and a long entry ran it out of memory.

### 3.6 Room

`write-elf` puts the whole environment in `DataRegion::io_page()`: 4096 bytes
(`linux_x86_64_image.hthr`). That page holds 64 word slots (512 bytes), every
buffer at its capacity, and a scratch range one byte longer than the largest
buffer (room for a path's NUL).
So all of a program's buffers together hold under 3.5 KiB, and one buffer
under 1.8 KiB. `sort`, `rev` of a long line, and `grep`'s line carried
across reads all need more. `word_slots()` is a constant 64, and the builder
will spend words fast on temporaries.

`write-elf` also never checks that the layout fits. `big_cat` (layout past
the page) was written and runs, but no theorem covers it:
`native_compile_correct` takes `fits` as a hypothesis, and the certificate
never discharges it. That is not unsound, since the certificate claims only
the bytes. But a user will read `write-elf`'s success as "this program is
correct", and today that reading is false for an oversized program.

**Fix.** The I/O profile takes its data size as a parameter. The ELF header's
`p_memsz` is a 64-bit field, so a large zero-filled segment costs nothing in
the file. The loader proof (`io_perm_in_segment`, now `i < 8192`) is stated
over the parameter. `word_slots` becomes a per-program number in `Layout`.
Every program then gets the data it declares, up to a fixed bound (a few MiB
is plenty). True allocation stays deferred (§7).

### 3.7 Numbers

Printing a count needs digits. The ISA model has no multiply, divide or
shift (`x86_64.hthr`'s `Instruction`: MOV, ADD, SUB, AND, OR, XOR, CMP,
SETcc, TEST and the immediate adds), and FunctionIR's shifts are refused at
lowering (`issues/verified-lowering-instruction-coverage.md`). Decimal output
can be done without them: subtract powers of ten in a bounded loop, from a
table of them, as the burned `%*d` formatter's loop did
(`native-proven-formatting-api`).
Decimal input can be done too: `10x` is `8x + 2x`, by doubling with `Add`.
So numbers are a library round in the builder, not an ISA round. The ISA
work (`verified-lowering-instruction-coverage`) helps code size and speed,
and can follow when `od`/hex output or performance asks for it.

### 3.8 What is not a blocker

- **Exit codes and fds.** `Exit(word)` works, and `Reads`/`Writes` take the
  fd as a word.
- **Data types beyond words.** For these tools, words plus byte buffers are
  enough. Records, lists and sum types are the builder's business (it lays
  them out in words and buffers), not the compiler's.
- **Calls between functions.** The builder inlines. Code size is the cost,
  and §3.2 pays for it. Procedures (`mrec`, design §10 item 2) earn their
  place when code size bites, not before.
- **Code speed.** The memory-resident code is slow, but it is correct and
  fast enough for a test suite. `native-compiled-code-shape` owns speed.

---

## 4. Tools against blockers

✗ marks a blocker the tool needs removed. The last row counts the ✗s.
"Builder" (§3.3) and "capacity" (§3.2) are marked only where the tool is past
toy size, roughly a page of `Source`.

| tool | bytes 3.1 | capacity 3.2 | builder 3.3 | leaves 3.4 | argv 3.5 | open 3.5 | room 3.6 | numbers 3.7 |
|---|---|---|---|---|---|---|---|---|
| true/false, cat, head -c | | | | | | | | |
| yes [STR] | ✗ | | | | ✗ | | | |
| echo | ✗ | | | | ✗ | | | |
| basename/dirname | ✗ | | ✗ | ✗ | ✗ | | | |
| tr (fixed sets) | ✗ | | | ✗ | | | | |
| rev | ✗ | ✗ | ✗ | ✗ | | | ✗ | |
| cat FILE… | ✗ | | ✗ | | ✗ | ✗ | | |
| head -n N | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | | ✗ |
| wc [-clw] [FILE…] | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | | ✗ |
| cmp | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | | ✗ |
| grep -F | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | |
| sort | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | |
| **tools blocked (of 14)** | **11** | **6** | **8** | **8** | **9** | **6** | **3** | **3** |

The first row's three tools are the three that work today. The other eleven
all need bytes.

The order in §0 follows the table, with two adjustments:

- **argv before bytes would buy nothing.** Every tool that needs argv also
  needs bytes, so bytes goes first.
- **Capacity and the builder rank above argv and open,** although they block
  fewer tools on paper. They are what make the *next* program cheap to write
  and build. Without them each later round's example program is a hand
  project, and the round after that hits the wall.

---

## 5. What a tool will look like

Once §6's rounds 1–5 land, `tr a-z A-Z` is this, built by `write-elf` with no
proof:

```heather
fn upper() → Prog {
    program(buffers := [buffer("in", 1024)], body := forever(
        read(stdin(), "in", "n")
            .on_failure(exit(1)).on_end(exit(0))
            .then(for_bytes("in", "n", λ b => if_(b.between('a', 'z'), b - 32, b)))
            .then(write_all(stdout(), "in", "n").on_failure(exit(1)))))
}
fn upper_source() → Source { upper().lower() }
```

The spellings are illustrative. The builder round fixes them. What matters
is that word ids, leaf splitting and loop bits are gone, and the byte map is
a bounded FunctionIR loop.

---

## 6. The rounds, in order

Each round is a self-contained thread with its own issue (all
`area: heather-in-heather`, `milestone: hih-tools`). Rounds on the same line
can run in parallel, since their code footprints are disjoint.

| # | issue | scope | done when | can run beside |
|---|---|---|---|---|
| 1 | `native-source-bytes` (re-scopes `function-ir-buffer-state-edges`) | `Load`/`Store` nodes on buffer state edges, `eval` over buffers, the memory-resident compile of a leaf with byte nodes, initial buffer bytes | `tr a-z A-Z` (sets fixed at build) and `yes` built by `write-elf` and run against GNU on random input | 2, 3 |
| 2 | `native-compile-capacity` | attribute write-elf's peak, read back in pieces, emission per statement if the kernel needs it, `--timings` on `write-elf` | a 64 KiB-code program builds under the suite's rail, with its scaling shape recorded | 1, 3 |
| 3 | `native-elf-every-program` | write-elf checks `fits`, states the program's `SimProgram` theorem (the generic form of `cat_native_simulates`) in every certificate, names why a compile is refused, and imports the certificate's modules itself | `head -c 10` gets its theorem with no per-program proof, and `opens` is refused with a reason | 1, 2 |
| 4 | `native-compile-wider-leaves` (re-scoped) | memory-resident compile of `Sequence`, `Compose`, `Conditional` and `Loop` regions, with no register-pool limit, and S4's lowering kept where it applies | `tr`'s byte map as a bounded FunctionIR loop, and a 40-node leaf | 5 |
| 5 | `native-source-builder` | the builder library, its lowering to `Source`, reflected pure helpers inlined, and write-elf's `<s>_lowered` step | `tr` and `head -c N` rewritten in the builder, and a `wc -l` (count only, exit status as the count mod 256) | 4 |
| 6 | `native-source-argv` (with `io-image-process-stack`) | `Source::denote(args)`, `argc`, `Arg(k, buf, len)`, the stack region and RSP at entry | `echo` and `yes STR` | 7, 8, 9 |
| 7 | `native-compile-other-calls` (exists) | `open`, `close`, path NUL in scratch | `cat FILE…` with GNU's diagnostics and exit status | 6, 8, 9 |
| 8 | `native-data-capacity` | the I/O profile's size as a parameter, per-program word slots | a program with a 1 MiB buffer runs and carries its theorem | 6, 7, 9 |
| 9 | `native-decimal-io` | decimal format and parse in the builder's library, on add/sub only | `wc -c` prints its count, and `head -n N` parses N | 6, 7, 8 |
| 10 | `native-tools-suite` | the §2 tools in `lib/native/tools/`, each tested against GNU under `LC_ALL=C` (`crates/cli/tests/native_tools.rs`, outside the fast lane) | the fourteen tools pass. **This closes `hih-tools`.** | — |

Rounds 1–3 can start today. Round 5 can start beside 4 against today's
leaves and pick up 4's forms as they land. Rounds 6–9 each need only 1 and 5.

---

## 7. Deferred on purpose

- **Register-resident words, word-wise copies**
  (`native-compiled-code-shape`). Speed, not reach. Words in registers
  landed 2026-10-28 (`docs/native-register-allocation-design.md`): checked
  homes cut about a third of each tool's code.
- **Procedures that make calls** (design §10 item 2, `mrec`). Inlining
  covers the target set, and procedures come when code size, not capacity,
  is the wall.
- **Allocation** (`hih-memory`: `mmap`/`brk` events, metering). A
  per-program data size (round 8) covers every §2 tool. Allocation is
  `hih-first-alloc`'s own milestone.
- **The uniqueness surface** (`effects-direction`). It is the right long-term
  front end, and it lands on round 5's builder. Building it first would put
  a language design round in front of every tool.
- **`stat`, and `wc`'s width rule from file sizes.** The old `wc` matched GNU's
  column width by stat-ing operands (`docs/native-wc-command-design.md`
  §2). The suite can pin `wc`'s format to the cases that need no stat (one
  count, or stdin), or the round can add stat then.
- **Liveness** (a tool that must never hang). The fuel-cut trees state
  partial correctness only, which is what every claim in this plan means.

---

## Appendix: the probes

The probe file, as run (its imports trimmed to the two that matter; `write-elf`
also needed the certificate's modules imported, §1). Each name was built with
`heather write-elf probes.hthr <name> -o <out> --cache-dir <dir>`.

```heather
import native_source;
import native_cat;

// exit 3, nothing else.
fn exit3() → Source { Source(functions := [], buffers := [], main := Then(ops([Const(64, 0, 3)]), Exit(0))) }

// cat to stderr.
fn cat_err() → Source {
    Source(functions := [], buffers := [512],
        main := Then(Then(cat_setup(512), ops([Const(64, 1, 2)])), Repeat(cat_pass(), 15)))
}

// head -c N: words as cat's, 2 the bytes still to copy, 20/21 scratch.
fn head_pass() → Stmt {
    Then(Invoke(Reads(0, 0, 2, 3)),
        Then(ops([SignedLessThan(64, 7, 3, 16), Equal(64, 8, 3, 16)]),
            Branch(7, Exit(10),
                Branch(8, Exit(11),
                    Then(ops([Const(64, 4, 0), Move(64, 5, 3)]),
                        Then(Repeat(cat_write(), 14),
                            Branch(12, Exit(10),
                                Then(ops([Sub(64, 21, 2, 3)]),
                                    ops([Move(64, 2, 21), Equal(64, 20, 21, 16), BitXor(1, 15, 20, 19)])))))))))
}

fn head_c(n: Nat) → Source {
    Source(functions := [], buffers := [512], main := Then(Then(cat_setup(512), ops([Const(64, 2, n)])), Repeat(head_pass(), 15)))
}
fn head10() → Source { head_c(10) }

// Refusals expected.
fn opens() → Source { Source(functions := [], buffers := [16], main := Invoke(Opens(0, 1, 2))) }
fn big_cat() → Source { cat(2048) }
fn wide_leaf() → Source {
    Source(functions := [], buffers := [], main := Then(ops([Const(64, 0, 0), Const(64, 1, 1), Const(64, 2, 2), Const(64, 3, 3),
        Const(64, 4, 4), Const(64, 5, 5), Const(64, 6, 6), Const(64, 7, 7), Const(64, 8, 8), Const(64, 9, 9), Const(64, 10, 10),
        Const(64, 11, 11), Const(64, 12, 12), Const(64, 13, 13), Const(64, 14, 14)]), Exit(14)))
}

// Size probes: cat's pass inlined k times in its loop.
fn passes(k: Nat) → Stmt { match k { Zero => cat_pass(), Succ(j) => Then(cat_pass(), passes(j)) } }
fn cat_x(k: Nat) → Source {
    Source(functions := [], buffers := [512], main := Then(cat_setup(512), Repeat(passes(k), 15)))
}
fn cat_x2() → Source { cat_x(1) }
fn cat_x4() → Source { cat_x(3) }
fn cat_x8() → Source { cat_x(7) }
```
