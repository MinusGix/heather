# `wc` as a command — design

> **Burned in B1 (2026-10-21).** The code this document describes was deleted with the
> hand-proved process stack (`docs/native/native-program-logic-design.md` §3.1); the document
> stays for its reasoning. The last commit with the code is `189659d` (tag `native-v0`).

Status: **design, 2026-10-03; nothing built.** Anchor issue:
`issues/native-wc-as-a-command.md`. It follows the author-ergonomics round
(`docs/archive/native-programs-read-like-programs-design.md`), which named it as the
next item on the program line. The trace model's general questions stay with
`issues/linux-syscall-trace-model.md`. This round adds three events to it and
assumes only that each event carries its response and that a claim
quantifies over histories.

## 1. What this round does

The certified `wc` reads stdin, prints `%7d %7d %7d\n`, and is correct only
for counts below 10^7. A user's `wc` takes file operands and flags and
prints a total. This round turns the stream filter into a **command**: it
runs over each operand named on the command line, prints one row per
operand and a total, and decides at run time which counts to print. The
claim covers every command line and every response Linux can give.

Five capabilities are new. Each is a slice (§10):

1. **argv on the initial stack**, as the process's entry state (§4.1).
2. **`openat`, `close` and `newfstatat`** as trace events with failure
   responses (§4.3).
3. **A run over several inputs.** The filter runs once per operand, and the
   per-file counts are added into totals (§6).
4. **Flags** that pick which columns are printed. The choice is made at run
   time, not when the program is built (§3.2).
5. **Counts of any size**, through one `%*d` formatter proved once in the
   library. It replaces the generated `%7d` words (§7).

The step stays the same. `wc_step`, its four per-byte lemmas and its
generated step piece don't change. Everything new is library code proved
once, plus the producer's layout. §9 shows why that matters for cost: a cold
build of the full `wc` should cost *less* than today's stdin-only `wc`, and
a warm build only slightly more.

## 2. The target: GNU `wc` 9.4 under `LC_ALL=C`

The tests compare against the host's `wc`, so GNU's behaviour is the target.
Everything below was checked on coreutils 9.4 (`strace` for the syscalls).

| command line | GNU prints | why |
|---|---|---|
| `wc f1` | `2 3 6 f1` | width from the operands' sizes: f1 is 6 bytes, one digit |
| `wc f1 f2` | ` 2  3  6 f1` / ` 1  2 12 f2` / ` 3  5 18 total` | sizes total 18, two digits; total line when there are two or more operands |
| `wc -l f1` | `2 f1` | one operand and one count: no padding, and no `stat` at all |
| `wc -lc f1` | `2 6 f1` | columns always print in the fixed order lines, words, chars, bytes |
| `wc -c -m f1` | `6 6 f1` | chars and bytes are separate columns; in the C locale they are equal |
| `wc f1 nosuch f2` | rows for f1 and f2, then a total, exit 1 | a failed open prints a diagnostic on stderr, no row, and continues |
| `wc /tmp` | `      0       0       0 /tmp`, exit 1 | open succeeds and read fails with EISDIR. The row shows the counts so far. Not a regular file, so the width is at least 7 |
| `printf x \| wc` | `      0       1       1` | stdin is a pipe, so width 7. No operand, so no name and no total |
| `wc < f1` | `2 3 6` | stdin is a regular file, so the width comes from its size |
| `wc - f1` | `-` is stdin, named `-` | |
| `wc -- -l` | `-l` is a file name | `--` ends the options |
| `wc -x` | usage on stderr, exit 1, no stdout | every option is parsed before any file is opened |
| `wc f1 -l` | `2 f1` | options may come after operands (GNU permutes) |

The syscalls GNU makes for `wc f1 nosuch f2`, in order:

- one `newfstatat(AT_FDCWD, name, &st, 0)` per operand, all made up front
  (`fstat(0)` for `-` or no operand);
- then for each operand: `openat(AT_FDCWD, name, O_RDONLY)`, reads until the
  empty read, the row's `write(1, …)`, and `close`.

**The width rule** (`compute_number_width` and `get_input_fstatus` in
coreutils' `wc.c`):

- One operand and one selected count: no `stat`, width 1.
- Otherwise, every operand is stat'ed, and the width is the number of
  decimal digits of the regular files' sizes added together (as a
  `uintmax_t`, so modulo 2^64). It is at least 7 if any operand that
  stat'ed is not a regular file. A failed stat adds nothing, wherever it
  is: `wc nosuch big` pads to big's size. (This said the width was 1 when
  the first stat failed; `compute_number_width` tests whether a stat was
  *made*, not whether it succeeded, and coreutils 9.4 on the box agrees.)
- Counts wider than the width print in full: the width is a minimum.

**Deviations, chosen.** The claim states what *this* program does, so each
of these is a fact about the program, not a hole in the claim:

- **No diagnostics on stderr.** A failure sets the exit status to 1 and
  writes nothing to fd 2, as `wc -l` already does (the decision of
  2026-09-27). Messages need a `strerror` table and `quotef`; filed as
  residue (§11).
- **A failed write exits 1 at once.** GNU's buffered stdout carries on with
  the remaining operands and reports the failure at `close_stdout`, then
  exits 1. Both exit 1. The difference is what runs after the failure: GNU
  may still write later rows (a write that fails once need not fail again),
  and this program stops.
- **Only `-l`, `-w`, `-m`, `-c`, bundles of them, `--` and `-`.** A long
  option (`--lines`), `-L` or `--files0-from` is an invalid option: exit 1,
  no stdout. GNU accepts them. This is residue.
- **A name containing a newline** is printed as it is. GNU shell-quotes it
  (`quotef`). This is residue.
- **`-c` on a regular file always reads it.** GNU may take the size from
  `fstat` instead. Stdout is the same unless the file changes while it is
  read; the claim covers whatever the reads return.

## 3. The program, as its author writes it

### 3.1 `wc.hthr`

The step, the state, the predicates, what the counts mean and the four
per-byte lemmas stay exactly as they are today. What changes is the bundle
at the end:

```heather
// The columns GNU prints, in its order, with the letter that selects each
// and what it means. In the C locale a character is a byte.
fn wc_columns() → List<Column<WcState>> {
    [Column('l', λ s => s.lines, wc_lines), Column('w', λ s => s.words, wc_words),
     Column('m', λ s => s.bytes, wc_bytes), Column('c', λ s => s.bytes, wc_bytes)]
}

// With no option: lines, words and bytes.
fn wc_command() → Command<WcState>(counting(wc_step), WcState(0, 0, 0, False),
    [λ s => s.lines, λ s => s.words, λ s => s.bytes], wc_columns(), [True, True, False, True]) {
    let zero = WcState(0, 0, 0, False);
    Command(columns_compute(…,
        fold_counts_filtered(wc_step, λ s => s.lines, newline, lines_step, zero, refl),
        fold_counts_runs(wc_step, λ s => s.words, λ s => s.inside, space, words_step, inside_step, zero, refl, refl),
        fold_counts_len(wc_step, λ s => s.bytes, bytes_step, zero, refl)))
}
```

The program's own proof obligation is the same as today: each column's count,
folded from the zero state, is what the column means. `wc_out` and
`three_fields_line` drop out of the example. `wc_l.hthr` stays as a stdin
filter: it is what `native_read_loop`'s tests and mutation controls build,
and the `Line` finish's only client, even though `wc -l` is now this binary
with a flag.

### 3.2 The bundle and what the command prints (`lib/command_program.hthr`, no x86)

```heather
// One printed column: the option letter that selects it, the state's count,
// and what that count means over an input.
record Column<C>(letter: BitVec(8), count: C → Nat, means: List<BitVec(8)> → Nat)

record Command<C>(step: C → BitVec(8) → Filtered<C>, init: C, counts: List<C → Nat>,
    columns: List<Column<C>>, default: List<Bool>) {
    advances: … := { split_all; all_goals { omega } },     // as Filter's
    computes: (input: List<BitVec(8)>) → ColumnsMean(columns, filter_state(step, input, init)),
}
```

The command line, as a function of argv (`args` is argv without argv[0]):

```heather
inductive Parsed { Refused, Selected(selection: List<Bool>, operands: List<List<BitVec(8)>>) }
fn parse_args(letters: List<BitVec(8)>, default: List<Bool>, args: List<List<BitVec(8)>>) → Parsed
```

- An argument that starts with `-`, is longer than one byte and comes before
  `--` is an option. Each of its letters must be a column's, and it selects
  that column. Any other letter makes the result `Refused`.
- `--` ends the options. Every later argument is an operand.
- Any other argument is an operand, `-` included.
- If nothing is selected, `default` is used.

What happened to each operand comes from the history (§5). The spec reads
only what a reader of GNU's code would read:

```heather
inductive StatSeen { NotAsked, StatFailed, Regular(size: Nat), Other }
inductive Opened { OpenFailed, Read(input: List<BitVec(8)>, clean: Bool) }
record Outcome(stat: StatSeen, opened: Opened)

fn command_width(selection, operands, outcomes) → Nat      // §2's rule, word for word
fn row(width: Nat, values: List<Nat>, name: Option<List<BitVec(8)>>) → List<BitVec(8)> {
    // first value pad_left(width, ' ', decimal(v)), each later one ' ' ++ pad_left(…),
    // then ' ' ++ name when there is one, then '\n'
}
fn command_stdout<C>(command: Command<C>, args, outcomes) → List<BitVec(8)>
fn command_status<C>(command: Command<C>, args, outcomes) → Nat   // 0 or 1
```

- `command_stdout` is one row per operand whose open succeeded, with the
  selected columns' `means` over the bytes read. A read that failed still
  gets its row, over the bytes read before the failure. When there are two
  or more operands, a `total` row follows with the sums.
- No operand means one unnamed row over stdin.
- `command_status` is 1 if parsing refused the command line or any open,
  read or close failed. Otherwise it is 0.

Both are total functions over plain lists. A reader checks them against §2
without reading any x86.

## 4. The process model

### 4.1 argv on the initial stack

Linux's x86-64 entry state, from the psABI (§3.4.1), is: RSP points at
`argc` (8 bytes), then `argc` pointers, then a null word, then envp and auxv.
The strings live higher up, each ending in a NUL byte. Their addresses vary
from run to run (ASLR), so the claim quantifies over the layout:

```heather
// The initial stack holds `args` (argv, argv[0] included) at `rsp`, readable
// through `read`: argc, then each pointer, each string's bytes, then its NUL.
fn ArgvAt<M>(read: M → BitVec(64) → Option<BitVec(8)>, memory: M, rsp: BitVec(64), args: List<List<BitVec(8)>>) → Type
```

Each string has no NUL byte inside it, and every byte that `ArgvAt` names
can be read. The claim is universal over `rsp`, the pointers and the args,
so no run can depend on where Linux put them. Envp and auxv are never read,
so they are not modelled.

### 4.2 Memory

`IoMemory { file, page }` gains two fields:

- **`frame: Nat → BitVec(8)`**, a second RW page at `0x411000`. The read
  page holds the input chunk and then the row being printed, so the
  command's own variables need a page of their own (§6.2). The ELF header's
  RW `PT_LOAD` grows from 4096 to 8192 bytes of memsz. It stays one segment,
  and the model splits it by address.
- **`rest: BitVec(64) → Option<BitVec(8)>`**, a read-only view of every
  address outside the file's window and the two pages. The initial stack
  lives there. `io_read` falls through to it where it returns `None` today.
  `io_store` and `IoWritable` never touch it, and code is fetched only from
  the file, as now.

`io_initial` quantifies over `frame` and `rest` as it does over `page`. A
process that never reads outside its pages, which is every program today,
gets one more universally quantified argument and nothing else (V1).
As built, both fields sit in the file's image rather than beside the page
(§10's C1 status).

**A new x86 form: `WordLoad`**, `MOV r64, [base]` (`REX.W 8B /r`, mod=00).
It is the read twin of `WordStore`: it reads eight bytes through
`ByteReadAccess`, little-endian. The argv pointers, `argc`, the frame's
variables and the formatter's table of powers of ten are words. It has the
same base restrictions as the byte store (no RSP, R12, RBP or R13, which
need a SIB byte or mean RIP-relative), so code that reads through RSP copies
it to another register first.

### 4.3 Three new events (`lib/std/os/linux/linux_x86_64_io.hthr`)

```heather
inductive OpenResult  { Opened(fd: Nat), OpenFailed(errno: Nat) }
inductive CloseResult { Closed, CloseFailed(errno: Nat) }
inductive StatResult  { Stated(st: List<BitVec(8)>), StatFailed(errno: Nat) }
inductive StatTarget  { StatPath(path: List<BitVec(8)>), StatFd(fd: BitVec(64)) }

// LinuxEvent gains:
//   OpenEvent(path: List<BitVec(8)>, result: OpenResult)
//   CloseEvent(fd: BitVec(64), result: CloseResult)
//   StatEvent(target: StatTarget, result: StatResult)
```

| event | at the SYSCALL | after |
|---|---|---|
| `OpenEvent(p, Opened(fd))` | RAX = 257, RDI = `AT_FDCWD` (−100), `p ++ [0]` readable at RSI with no NUL in `p`, RDX = 0 (`O_RDONLY`) | RAX = fd, any `fd < 2^31` (quantified) |
| `OpenEvent(p, OpenFailed(e))` | same | RAX = `errno_word(e)` |
| `CloseEvent(fd, …)` | RAX = 3, RDI = fd | RAX = 0, or `errno_word(e)` |
| `StatEvent(StatPath(p), Stated(st))` | RAX = 262, RDI = −100, path as for open, RDX = buffer, R10 = 0, 144 bytes writable at RDX | `st` (any 144 bytes, quantified) stored at RDX, RAX = 0 |
| `StatEvent(StatFd(fd), Stated(st))` | RAX = 5, RDI = fd, RSI = buffer | same, at RSI |
| `… StatFailed(e)` | same | RAX = `errno_word(e)`, junk at the buffer as for a failed read |

RCX and R11 are quantified after every event, as they are today. The
returned fd is quantified rather than "the lowest free one". That is weaker
than Linux promises and is all the program needs. The read event already
carries its fd, so reading from an opened file needs no new rule. Only the
read head changes (§6.1).

**What a stat says** is a function of the bytes Linux stored, as C reads them
(x86-64 `struct stat`, checked with `offsetof` on the box): `st_mode` is the
`u32` at 24 and `st_size` the `i64` at 48. `stat_regular(st)` is
`(mode & 0o170000) = 0o100000`. The spec's `StatSeen` is computed from `st`
by those two functions, so the claim trusts no reading of a stat beyond
C's.

## 5. The claim

The environment's behaviour is a history with one entry per phase:

- **the command line:** `args` and their stack layout (`ArgvAt`);
- **the stat pass:** one `StatResult` per operand, or none when §2 says no
  stat is made;
- **per operand:** an `OpenResult` (none for `-` or no operand), then the
  read steps and ending (today's `EofStep`/`EofEnd` on that fd), then the
  row's write steps, then a `CloseResult` (none for fd 0);
- **the total row's write steps**, when there is one.

Well-formedness is per step, as today: chunks of 1 to 4096 bytes, partial
writes below what is left, errnos in 1 to 4095 and not EINTR where EINTR is
retried. Open and close don't retry EINTR, because GNU doesn't.

For the built file, every history and every initial `page`, `frame`, `rest`,
`gprs` and `flags` that satisfy `ArgvAt` at RSP:

```text
LinuxRuns(io_linux(), command_events(…), io_initial(file, page, frame, rest, gprs, flags))
```

The library states two corollaries, so no reader unfolds
`command_events`:

- **stdout.** On a run with no failed write, `sent_to(1, events)` is
  `command_stdout(command, args, outcomes(history))`.
- **status.** On such a run, the last event is
  `ExitEvent(command_status(…))`. On a run with a failed write, it is
  `ExitEvent(1)` right after the failing write.

The premise that bounds the counts is `FilterRoom` lifted to the run: all
operands' inputs together, plus slack, are below 2^64, because the totals
are the sums. As today, `_runs_every` gives determinism over the same
responses.

## 6. The process (`lib/elf64_command.hthr`)

### 6.1 Code, in phases

```
entry:   frame.argv ← RSP                         (MOV RBX, RSP; WordStore)
scan:    for each argv[1..]: classify (option / -- / operand), set bits in
         frame.selection, count operands; a bad letter → exit(1)
         empty selection → default
width:   unless one operand and one count: stat each operand (StatPath, or
         StatFd(0) for - / none) into frame.st; add regular sizes; note a
         non-regular one and whether the first failed; width = digits(total),
         raised to 7, or 1
operand: for each operand (or stdin once):
           fd ← 0 for - / none, else openat; failure → status 1, next operand
           zero the state registers                (state_init_block)
           read loop: the filter's loop, the read head taking RDI from frame.fd
             end of file → row;  failed read → status 1, row
           row:  the state's counts → frame.counts (one WordStore each)
                 for each selected column: %*d at the cursor, ' ' before all but the first
                 ' ' and the name: a separate write from argv's own bytes
                 '\n'; frame.totals += frame.counts
           close unless fd 0; failure → status 1
total:   if two or more operands: the total row from frame.totals, name "total"
exit:    exit(frame.status)
```

Three things are reused as they stand: the per-byte loop and the step piece
(`elf64_read_filter`), the write loop (`elf64_write_loop`, which already
takes its buffer and length in R9/R10), and the read head's retry and
failure blocks. Two things change:

- **The read head** takes its fd from the frame: `MOV RDI, frame.fd`'s
  address, then `WordLoad RDI ← [RDI]`, where today it is `MovRI(Rdi, 0)`.
  RDI is free at the read. Stdin-only filters keep today's head.
  As built, the fd stays in RSP and the head copies it (§10's C1 status).
- **The driver** (`eof_run`) gains the fd as a parameter (today it is the
  literal 0) and a continuation for a failed read (today it is
  `[ExitEvent(1)]`). The filter instantiates them with 0 and the exit, so its
  trace is unchanged. This is the same kind of change as §3.1 of the
  stream-filter design, where `seen` was added.

**The name is written straight from argv.** A row is the counts, then
`' '` and the name, then `'\n'`. The name can be up to `MAX_ARG_STRLEN` long,
so it is not copied into the page. The process writes the counts part from
the page, then the name from its argv address, then the newline. That is
three writes where GNU makes one, and `sent_to` concatenates them, so stdout
is the same. The name's length comes from a NUL scan during `scan`, kept in
the frame. The write loop's `LinuxWritesFrom` reads through `io_read`, which
already reaches `rest`.

### 6.2 Registers and the frame

The read loop uses every register but RSP: RSI, RCX, RDI and R12 for the
loop, R13–R15 and R8 for the state, and the rest as the step's scratch. So
**nothing outlives an operand in a register**. Between operands everything
lives in the frame page: argv base, argc, the argument cursor, the current
fd, selection, width, status, operand count, the stat pass's running total
and flags, the per-file counts, the totals, the name pointer and length, and
the 144-byte stat buffer. Each phase loads what it needs with `WordLoad` and
stores back with `WordStore`. The frame is accessed only between reads,
never in the per-byte loop, so it costs nothing per byte.

**Columns are a table.** The producer lays out the program's column table in
the file: for each column, its selection bit and the frame slot of its
count. It also emits one `WordStore` per count, which spills R13–R15 to the
frame. The row loop is library code. For each column it tests the bit, loads
the slot, and calls the formatter. No column-specific code is generated.

## 7. The formatter: `%*d`, once, in the library

Today's `%7d` is two generated words per field (`field_low`, `field_high`),
each a restoring-division chain of `place`/`mark` steps that the structured
generator lowers and certifies. They are limited to 10^7 and are the
largest item in a cold build: about 15.7k generated declarations, 47% of the
item time (`issues/x86-certificate-per-declaration-constant.md`, log of
2026-10-03). Scaling that design to 20 digits and a run-time width would
multiply the place steps about 2.5× and still be per format.

Instead, the command's formatter is **a hand-written library loop**, proved
once like the write loop and placed at an offset:

```
digits:  k ← 20; while k > 1 and n < pow10[k-1]: k ← k − 1        (table in the file, WordLoad)
pad:     while width > k: store ' ', cursor +1, width −1
emit:    for each place from pow10[k-1] down to 1:
           d ← 0; while n ≥ place: n ← n − place, d ← d + 1   (at most nine times)
           store '0' + d, cursor +1
```

- **Spec:** the bytes from the cursor are `pad_left(width, ' ', decimal(n))`,
  over decimal_line's existing `decimal` and `pad_left`, for every
  `n < 2^64` and every width.
- **Proof shape:** three loops, each an induction like `write_from`. Each
  iteration is a fetched block plus one `ByteStore` or `CmpRR`/`SetBelow`
  test, with arithmetic lemmas as small named theorems (the `eof_room`
  pattern, because `omega` inside match arms refuses facts it can't spell).
  The invariant of `emit` is `n = (original mod 10·place)` with the digits
  so far stored. It is decimal_line's `places` identity, stated over a
  table.
- **No division instruction** is needed. Repeated subtraction runs at most
  nine times per digit, so at most 180 iterations for a 20-digit count.
  That is noise beside the read loop.
- **Branches** use the existing `CmpRR; SetBelow; TestRR; JZ`. The flags are
  not fused here: `issues/native-narrow-compare-fusion.md`'s fused forms are
  the structured generator's, and this code is written by hand. Code size
  is not the point of this loop.

This is the first piece of `issues/native-proven-formatting-api.md`. It
gives POSIX `%d` as the width-1 case. Stdin filters keep `Line`. `Fields`
loses its only client when `wc.hthr` becomes the command, so C4 deletes it
(§11, decision 6).

**Status (built, 2026-10-04): `lib/elf64_format_width.hthr`.** It differs
from the sketch above in two ways, both to keep the proof small and off the
model work of C1:

- **Unrolled places, no table and no `WordLoad`.** Each of the nineteen
  places above the units is a block of its own with its power of ten as an
  immediate (`MovRI(R11, place_word(i))`): a run of `count_block`s counts the
  places the number reaches, the padding loop stores spaces while that count
  is below the width, and a run of `emit_block`s writes one digit per place,
  each skipping its place while the whole count is below it (so a leading
  place prints nothing and an inner zero prints `0`). The code is fixed bytes,
  position-independent, and needs no new decoder form.
- **Branches on the carry**: `CmpRR` then `JumpIfNear(B | AE, …)`, the
  borrow of `CmpRR` read directly as unsigned less-than, instead of
  `SetBelow; TestRR; JZ`.

Interface: RAX holds the count, RDX the width, RDI the cursor into the I/O
page; RAX, RBX, RCX, RDX, RSI, RDI, R11 and the flags are clobbered, the
other nine registers kept. The claim is `format_runs`: placed anywhere in
the file, with room in the page, the code runs to its end and the page holds
`padded_decimal(width, n) = pad_left(width, ' ', decimal(n))` at the cursor,
for every 64-bit `n` and every width. Its spec half proves that the unrolled
place digits equal `decimal` (`decimal_of_places`). Proof cost is linear in
the number of places, and is paid once, in the library; a program adds only
its placement (`crates/elab/tests/format_width_process.rs`). Nothing uses it
yet: the generated `Fields` finish stays until C4 migrates `wc`.

## 8. Producer and generator

- **Generator: no change.** The step piece is generated over the context's
  step exactly as for a `Filter`. A `Command` is reflected through its step,
  so `{p}_step_piece` is the same declaration set as today's `wc`.
- **Producer:** `crates/cli/src/native/read_command.rs`, beside
  `read_filter.rs`. `profile_of` routes a bundle whose type's head is
  `Command`. It lays out the phases of §6.1 around the step piece, emits the
  column table, the count spills and the layout and jump facts, and states
  `{p}_runs`, `{p}_runs_every`, `{p}_stdout` and `{p}_status`. It validates
  `columns` against `counts` (each column's count is one of the state's
  Nat fields) and `default`'s length.
- **No formatter module** is generated for a command (§7). `fields_format_*`
  stays for stdin `Fields` filters.

## 9. What the full `wc` adds to certificate cost

Measured shares come from a cold `build-x86` of today's `wc` (2026-10-03,
master at `200fb73`, after PR #2's `goal-world-copies-psi`), with
`--timings` on the cloud box at the default eight kernel workers. Shares are
of summed item time. At width eight the item times add up to more than the
run, but the shares agree with the width-one attribution logged on
`issues/x86-certificate-per-declaration-constant.md` to within a few points.
Item counts are exact. Everything for the command is an estimate by analogy
with the closest existing module.

### 9.1 Today's cold `wc`, by part

| part | items | share |
|---|---|---|
| the `Fields` formatter's two certificates (`fields_format_*`) | 15,681 | 47% |
| bundled library | 3,382 | 29% |
| the program's own proofs (`wc` module) | 27 | 14% |
| the step piece (`wc_program_native_piece_*`) | 2,360 | 9% |
| the process certificate | 333 | 1% |

Library cost is concentrated. `elf64_read_filter` is 128 items and a third
of the library's share (10% of the build). Most of that is four
loop-composition proofs: `filter_after_close`, `filter_loop`, `filter_chunk`
and `filter_byte`. A register-only loop costs far less: `elf64_write_loop`
is 75 items and 0.6%. Per item, the filter's loop module costs about ten
times the write loop's.

### 9.2 The full `wc`, by part

| part | today | full `wc` | why |
|---|---|---|---|
| program proofs | 14% | about the same | the same step and lemmas; the bundle names four columns instead of a `Fields` finish |
| step piece | 9% | **unchanged** | the same `wc_step`, so the same piece |
| formatter | 47% | **gone** | §7: the `%*d` loop is library code |
| bundled library | 29% | +14 to +20 points | §9.3 |
| process certificate | 1% | about 3–4% | more phases, so more pieces placed and more jumps to state |
| **cold build, whole** | 100 | **about 70–80** | |
| **warm build** (library and formatter images cached, program edited) | ~24 | **about 26–28** | only the process certificate grows |

So **the full `wc` makes a cold build cheaper by about a quarter** and makes a
warm build about a tenth dearer. A cold build of *any* program that imports
the command library pays the new library once per image store. Programs that
don't import it pay nothing. The formatter's 47% was paid once per store
too, but only by `Fields` programs.

The formatter-certificate rework running in parallel (fewer, larger
declarations from `function_ir_x86_lower/structured_cert.rs`) still pays off
here. The step piece's 9% is made of the same generated families
(`*_decodes`, `*_correct`, `*_preserves`), and so is every stdin filter's.
The two changes are independent: this design removes the `%7d`
certificates, and that rework makes each generated piece that remains
cheaper.

### 9.3 Where the new library items come from

Each estimate counts top-level declarations in the closest existing module.
The timings' item counts run about 1.3–1.45× the declaration count (records
and matches generate items), so ~630 declarations is about 850 items.

| new library part | closest existing | its decls | estimate |
|---|---|---|---|
| `WordLoad` form (encode, decode, execute, uniqueness) | `x86_64_data_read` (ByteLoad) | 16 | ~20 |
| `IoMemory` `frame`/`rest`, `ArgvAt` | `elf64_io` | 43 | ~25 |
| open/close/stat events and their intros | `linux_x86_64_io`'s read/write rules | ~15 of 37 | ~20, plus determinism cases (~15) |
| argument scan (classify, NUL scan, option letters) | `elf64_write_loop` (one loop with arithmetic) | 52 | ~100 (two loops) |
| stat pass and width | `elf64_write_loop` | 52 | ~70 |
| `%*d` formatter (three loops plus the `places` identity over a table) | `elf64_write_loop` + `decimal_line`'s spec half | 52 + ~40 | ~150 |
| per-operand driver, read head on an fd, row and totals | `elf64_read_filter` | 100 | ~150 |
| `command_program` spec (`parse_args`, `command_width`, `row`, stdout and status) and its lemmas | `stream_filter` + `filter_program` | 40 | ~60 |
| claim and corollaries | `elf64_filter_finish` + `read_filter_runs` | ~10 | ~20 |
| **total** | | | **~630** |

They are priced by kind, not at the library average:

- **Plumbing** (model, events, spec, intros; ~300 items) at the cost of
  `linux_x86_64_io` or `elf64_io` per item: about 3 points.
- **Register-and-store loops** (two scan loops, the stat loop, the
  formatter's three, the column loop): each between `elf64_write_loop`
  (0.6%) and one of `elf64_read_filter`'s composition proofs (1–3%). Seven
  loops come to about 6–10 points.
- **The per-operand driver**, which composes the filter's read loop, the
  row, the close and the totals: priced like `elf64_read_filter`'s outer
  proofs, about 5–7 points.

**The uncertain line is the driver.** The filter's loop module costs ten
times the write loop per item, and the driver is the same kind of proof.
V4 and V5 (§10.1) are the early readings. If the driver costs twice the
estimate, a cold build is still cheaper than today's.

### 9.4 What to measure, and when

- **After C1** (the model), check the library's cold time per new module
  with `--timings` and compare with §9.3. A module far above its analogue is
  the signal to split its loop records (the `map_byte` lesson,
  `docs/archive/native-tr-design.md` §8).
- **After C4**, take one cold and one warm `build-x86` of the full `wc` with
  `--timings`, attributed with `scripts/timings`, and log it on
  `issues/x86-certificate-per-declaration-constant.md`. Seconds belong on
  the user's machine; counts and shares are fine on the cloud box.
- `native_wc` is the suite's closest test to the CPU rail. The command test
  builds once and runs many command lines against the one binary, so the
  build is shared across cases.

## 10. Slices

| slice | content | done when |
|---|---|---|
| C0 | probes V1–V6 below | each holds or the design is amended |
| C1 | model: `WordLoad`; `IoMemory.frame`/`rest`, the 8 KiB RW segment, `ArgvAt`; open/close/stat events and determinism cases; `eof_run` with fd and failure continuation | every existing process and test checks unchanged in meaning; a hand test opens, reads and closes one file |
| C2 | library pieces: argument scan, stat pass and width, `%*d` formatter, row writer, each at an offset with its own record of facts | an elab test runs each piece over abstract inputs; refusal controls (below) |
| C3 | `elf64_command`: the per-operand driver, the claim, the stdout and status corollaries; `lib/command_program.hthr` | an elab test composes the process over a hand-written step piece (as F2 did) |
| C4 | producer `read_command.rs`; `wc.hthr` becomes the command (`wc_l.hthr` stays, §3.1); the `Fields` finish, `elf64_read_fields`' tail, its producer path and `read_fields_process` are deleted | `build-x86` builds it; the CLI test runs §2's table against the host `wc` |
| C5 | (optional, the second client) `cat FILE...`: `mapping(id)`, no columns, no options | builds and matches host `cat` over files; shows the command shape is not `wc`-shaped |

C1's model change and C2's formatter don't depend on each other. The
formatter needs only `WordLoad` and a buffer, so the two can run in
parallel once `WordLoad` lands.

**Status (C1 built, 2026-10-04).** The model is in, and every existing
process checks with its trace unchanged. Where it differs from §4 and §6.1:

- **`frame` and `rest` live in the image, not beside the page.** `IoMemory`
  is `{ file: IoImage, page }` and `IoImage` is `{ bytes, frame, rest }`
  (`lib/elf64_io.hthr`). The read driver's obligations quantify over the
  page, because a read overwrites it; with the frame inside `file`, every
  existing lemma that keeps `file` keeps the frame across reads for nothing.
  `io_read` reads the file's bytes, then the frame at `0x411000`, then
  `rest`; `io_store` writes the frame by rewriting the image. `IoWritable` is
  the page or the frame, a disjunction, so existing proofs wrap their page
  case in `Inl`. Code is fetched only from `bytes`, as before. Every io
  program's RW segment is now 8 KiB of memsz; the code bytes are unchanged.
- **`WordLoad` takes any base.** It is encoded like `ByteLoad` (a SIB byte
  for RSP and R12, a zero displacement for RBP and R13), not restricted like
  the stores, so code can read `[RSP]` directly. A step needs all eight
  bytes below the canonical boundary (`base + 8 ≤ 2^47`) and reads them
  little-endian through the profile's byte access (`read_word`). The decoder
  tells `8B` from the stores in the same mod-00 branch, and
  `word_load_form_complete` keeps determinism's one-fetch-one-form argument
  whole. `word_load_ran` (`elf64_read_pieces`) runs one at an offset from a
  `WordAt` fact.
- **`ArgvAt`** (`lib/std/os/linux/linux_x86_64_io.hthr`) names the k-th stack word by
  value, `argv_slot(rsp, k) = rsp + 8k`, so a program that adds to RSP meets
  it through `toNat`. Each argument is a `CStringAt`: its bytes, then a NUL,
  with no NUL before it, all below the canonical boundary.
- **Events as §4.3.** Open and stat name their path by `CStringAt` at RSI.
  Open and close return through the write's return state (`open_rax`,
  `close_rax`), and a stat stores through `linux_stat_return`. In the
  determinism proof, two paths read from one memory are one path, because a
  C string ends at its first NUL (`c_strings_alike`). A stat of a path and a
  stat of an fd are told apart by their syscall numbers.
- **The fd is held in RSP, not loaded from the frame.** The read head's
  first instruction sets RDI from an `FdSource`: `MovRI(Rdi, 0)` for stdin,
  `MovRR(Rdi, r)` for a register. The driver takes the source and the fd,
  plus one obligation, `EofProcess.reads`: the invariant pins the fd's
  register. RSP is the only register the read loop keeps, so a command keeps
  its fd there, and the head needs no `WordLoad`. Stdin filters instantiate
  `FdStdin` and 0, so their traces are unchanged. Their head now sets RDI
  first, which reorders its bytes but keeps the length.
- **Hand test:** `crates/elab/tests/open_read_close_process.rs`. The test
  program opens argv[1], reads it to end of file through `eof_from` with the
  fd in RSP, closes it and exits 0. A failed open exits 1. The claim covers
  every file holding the code, every argv layout, page, register file and
  history. Four mutations are refused: opening argv[0], keeping the fd in a
  register the loop clobbers, closing RAX, and exiting 0 after a failed
  open. `linux_determinism.rs` gains refusals for a decoder that misses `8B`
  and for stat answers compared by kind or with unbounded junk.

**Status (C2's argument scan built, 2026-10-04): `lib/elf64_arg_scan.hthr`,
against `lib/command_program.hthr`'s `parse_args`.** C2 lands piece by piece;
the stat pass and the row writer follow. Where the scan differs from §3.2 and
§6.1:

- **The selection is a word, not a `List<Bool>`.** Column `i` is bit `i`,
  and an option ORs its letters' bits in, so the spec (`option_mask`,
  `letter_bits`) uses the machine's own `bor` and the code needs no bit
  arithmetic proved. `chosen_mask` applies the default when nothing is set.
- **Eight letter slots, fixed.** The letter table is eight position-
  independent slot blocks (`CMP AL, letter; JNE; RDX |= bit`), with NUL in
  the slots past the columns; no argument letter is NUL, so they never match.
  A fixed table keeps every jump around it a closed number, whatever the
  program's letters. A command has at most eight columns.
- **Registers only.** The scan keeps its state in registers and stores
  nothing: R8 ends as the selection and R9 as the operand count (as the word
  of the count; nothing bounds argc). The command stores them to the frame.
  It re-walks argv for the operands later, so it keeps no operand pointers.
- **argv ends at the null pointer.** The scan walks slots until the null
  word rather than counting argc, so `ArgvFrom` now says each argument's
  pointer is not null, as the psABI lays it out (a premise of the claim).
- **Claim:** `scan_runs` — placed anywhere in the file and entered with RSP
  at any argv layout, the scan exits 1 exactly when `parse_args` refuses, and
  otherwise runs to its end with R8 and R9 as `parse_args` gives; RSP, RBP,
  RCX and R12–R15 are kept.
- **Cost lesson.** The first proof of one argument's cases was one
  declaration whose machine states nested a dozen steps deep, and it
  dominated the module's cold time. Split into three lemmas that each start
  from an abstract state and a record of facts (`ArgAt`), the same proof
  is a few percent of it. Measuring a layout of forty pieces by a nested
  `⟨refl, …⟩` also grew faster than linearly; `measured_self` measures any
  layout by its own lengths, and one closed equation pins them.
  Test: `crates/elab/tests/arg_scan_process.rs` (a client placing the scan
  past any header; `parse_args` over §2's command lines; seven refusals).

**Status (C2's stat pass and width built, 2026-10-04):
`lib/elf64_operand_cursor.hthr` and `lib/elf64_stat_width.hthr`, against
`command_program`'s `operands_from` and `stat_width`.** Where they differ
from §6.1:

- **An operand cursor, shared.** The stat pass and the per-file driver both
  walk argv again, so stepping to the next operand is one library piece
  (`cursor_runs`): RBX the argv slot, R12 whether `--` has been seen, RSI
  the operand's pointer or zero at the end. It passes over options and `--`
  without reading their letters; `parse_operands` proves its operands are
  the ones `parse_args` gives, so the scan's verdict is not re-checked.
- **argv is named once, for every page.** Stats (and later reads) overwrite
  the page, so the cursor's premise names argv's pointers outside the
  per-page quantifier (`ArgvStays`): the same pointer holds whatever the
  page is.
- **The width is RSI, not the frame.** The pass keeps the total in R13, the
  other-kind flag in R14 and whether a stat was made in R15, stats into the
  page's first 144 bytes (nothing has been read yet), and ends by running
  the formatter's own digit-count blocks over R13, then the floor of 7. The
  command stores it.
- **The spec is three folds.** `stat_targets` (one target per operand, `-`
  as fstat(0), stdin once when there is none), `stat_seen` (a failed stat,
  a regular file's size, another kind) and `stat_width` over them; the
  claim `stat_runs` gives the events and leaves RSI as `stat_width` of
  Linux's answers. The one-operand, one-count case (no stat at all, width
  1) is the command's choice, not the pass's.
- **One elaborator gap cost a bisection.** A proof of a conjunction passed
  where an equation was expected got past the elaborator and was refused
  only by the kernel, at the whole declaration
  (`issues/elab-accepts-conjunction-for-equation.md`).
  Tests: `crates/elab/tests/stat_width_process.rs` (a client placing the
  pass past any header; targets, stat decoding and widths over §2's cases),
  `operand_cursor_refusals.rs` (two) and `stat_width_refusals.rs` (seven), a
  file each so each shard fits the suite's CPU rail.

**Status (C2's row writer built, 2026-10-04): `lib/elf64_row_fields.hthr`,
against `command_program`'s `row_counts`.** This finishes C2. Where it
differs from §6.1 and §6.2:

- **Only the counts.** The writer stores a row's fields in the page; the
  name and the newline are the driver's (C3), written after the fields
  straight from argv as §6.1 says. So one piece writes both a file's row
  and the total row.
- **Counts by slot, not a producer table.** The counts are eight words, one
  per column slot, at an address the caller passes in R12; column `i`'s
  count is slot `i`'s. The driver stores the state's counts into the slots
  (wc's `m` and `c` both get the byte count), so the writer needs no table
  of frame offsets and no generated code. `CountsAt` says the slots hold
  the counts at every page, since the formatter writes the page.
- **One formatter, in a loop.** R15 is slot `i`'s bit and doubles each
  round; R9 says whether a field has been written, for the space between
  fields. The loop ends when R15 reaches 256. RDI is the cursor throughout,
  as the formatter leaves it.
- **Claim:** `row_runs`: placed anywhere, with R12, R13 (the selection),
  R14 (the width) and RDI set, the writer stores `row_counts` at the cursor,
  leaves the rest of the page alone and moves RDI past it; RSP, RBP, R8 and
  R10 are kept. Room for eight fields of the width plus 21 bytes is a
  premise.
- Its kept registers are a `record` (`RowKept`) rather than a conjunction,
  per `issues/conjunction-facts-read-by-counting.md`.
  Tests: `crates/elab/tests/row_fields_process.rs` (a client placing it past
  any header; §2's rows) and `row_fields_refusals.rs` (seven).

**Status (C3 built, 2026-10-04): `lib/elf64_command.hthr`, with the
corollaries in `lib/elf64_command_output.hthr`.** Where it differs from §5,
§6.1 and §6.2:

- **Closed offsets, the step last.** The command is laid out at fixed
  offsets from the entry (`ca_*`), with every jump between its pieces a
  closed fact (`cmd_j_*`): the scan, the selection and count stores, the
  stat pass, the slot init, the operand loop, the read head, a file's row
  and tails, the failed-read finish, the total row, and the exit. The
  program's step piece and the chunk loop come last (`ca_core`), so only the
  step's own jumps depend on its length. The library pieces are placed whole.
  (2026-10-08, `issues/native-label-assembler.md`: the offsets are no
  longer literals. The command is a program over `x86_64_asm`, its items at
  labels `l_*`, and `ca(l)`, `cmd_d(l)` and the jump facts are computed from
  the items' lengths; the chunk loop is the program's last piece, at
  `l_core`. A jump fact is proved by evaluating both sides
  (`asm_jump_lands`), since meeting two offsets by conversion runs out of
  fuel once a jump spans much of the program, and the proof helpers state
  an offset several items on an item at a time, `(k + 10) + 3`, as a label
  is.)
- **Everything kept between operands is in the frame.** The read loop
  leaves no register but RSP, which holds the operand's fd (C1), so the
  driver keeps the rest in 24 frame slots (`elf64_frame`):
  - slots 0 to 7 hold a file's counts and 8 to 15 the totals;
  - 16 holds the selection, 17 the width and 18 the status;
  - 19 and 20 hold the cursor's argv slot and its `--` flag;
  - 21 holds the operand count, 22 the operand's name, and 23 whether it
    was opened, and so must be closed.
  A spill block per column stores the state's register and adds it into its
  total, so the row writer reads counts by slot, as C2 planned.
- **The name is measured at row time.** Its pointer is stored at the operand
  (slot 22), and its length is scanned to the NUL only when the row is
  written. Nothing about the name is kept in a register across the reads.
- **The operand loop is recursion on the operands.** `LoopGoes` is what runs
  at the loop's head for every frame holding the selection, width, count,
  cursor and the totals so far. The totals are fixed there, because what
  the operands after them need of the history depends on them (`FilesOk`).
- **Two premises beyond §5.** `argc < 2^31` keeps the operand count below
  2^64, so the word R9 holds is the count (Linux caps argc at
  `MAX_ARG_STRINGS`, 2^31 − 1). An opened name is 1 to 4095 bytes (`OpenOk`), since
  Linux's PATH_MAX counts the NUL and an empty path is ENOENT. Both hold of
  every real process.
- **The claim** is `command_runs`, against `command_events`. Any file whose
  bytes hold the command (`CommandPlaced`), entered at the ELF entry with
  RSP at any argv, runs every history Linux can give (`CommandHistoryOk`).
  `command_sends` and `command_exits` turn the events into what is written
  to stdout (`command_stdout`) and the exit (`command_status`), given that
  each write ran to its end (`CommandWritten`). The spec is a fold over the
  history's outcomes (opened or not, how the reads ended), not over the
  syscalls.
- **Cost lesson.** A declaration that both builds a freshly stored machine
  state and branches on a `match` over it grew far faster than either half.
  The prologue's store and test, the selection store and its few-operands
  test, and the total row's name writes each dominated the module's cold
  check. Split so that the stores end at an abstract state described by a
  record (`BeginStored`, `KeepStored`, `PutReach`) and the branch starts
  from it, each became a small share of the module.
- **The test's step piece is abstract, not hand-written.** The claim is
  stated over `FilterFacts`, so the test composes the whole process over any
  step piece the filter's facts hold of, with no code of its own. The
  generated piece (C4) is one instance.
  Tests: `crates/elab/tests/command_process.rs` (the composed process
  theorem; §2's rows, the total row and the exit statuses over a lines and
  bytes counter) and `command_refusals.rs` (four). Both replay the library
  as a semantic prefix (`support/command_prefix.rs`). Cold, that prefix is
  more than one process's CPU rail, so `scripts/test` populates it first in
  two bounded processes (`semantic_command_warmup`: the filter half to the
  stat pass, then the rest).

**Refusal controls** (mutations the library must reject), in the
`slow_acceptance_` tests as now: the row loop printing an unselected
column; the formatter's pad loop off by one (`width ≥ k`); the stat pass
summing a non-regular size; an open failure that leaves status 0; the total
row printed for one operand; the read head reading fd 0 after an open; the
name write using the NUL-inclusive length.

**Status (C4 built, 2026-10-05): `crates/cli/src/native/read_command.rs`;
`examples/x86-native/wc.hthr`'s `wc_command` is the command.** `build-x86`
builds it, and `crates/cli/tests/native_wc.rs` runs §2's table and a sweep
of piped inputs against the expected output and the host's `wc`. The
`Fields` finish, `elf64_read_fields`, its producer path and
`read_fields_process` are gone. Where it differs from §8:

- **The producer reads the program back, it does not restate it.** The
  bundle's written type gives the step, the state, the nullary function
  listing the columns and the default. The columns' letters, and which Nat
  field of the state each count is, come from evaluating the checked
  context: the counts are taken at a state whose Nat field `k` holds
  `k + 1`. It refuses no columns, more than eight, a default of the wrong
  length, a letter that is NUL, `-` or not a byte, and a count that is not
  one of the state's Nat fields.
- **The library's bytes come from the kernel's evaluator**
  (`native/evaluate.rs`): the program's bytes (`asm_code(cmd_fills(…),
  cmd_labels(), cmd_prog())`) and its items' lengths (`asm_lens(cmd_prog())`)
  are evaluated and split by the lengths, so no encoder of the library is restated in Rust.
  The certificate states the same bytes as literals, and the kernel
  re-checks them, so a misread list is refused there.
- **The frame's addresses are `BitVec::ofNat`.** `frame_at` was
  `word_of_nat(64, base + o)`, an iterated increment that neither the
  evaluator nor conversion can afford for an address near `0x411000`. It is
  now `BitVec::ofNat`, and `frame_counted` bridges the two forms where a
  proof still counts (`frame_step`, `slots_counts`).
- **The code is proved a piece at a time.** One declaration's fuel evaluates
  a few hundred encoded bytes, and the command's library code is several
  thousand. Each item is stated as written by `refl` where `asm_back`
  finds it in the program. An item above the bound (the scan, the stat pass, the
  rows) is stated a fixed-size chunk at a time (`ChunksAre`, `take` and
  `drop`), which needs nothing of how the item is made; until 2026-10-08 the
  producer named the long parts' own layouts and the formatter's appends
  instead. `asm_code_same` (x86_64_asm) joins the items into the
  program's code. A literal-list congruence over the whole
  list of parts hung conversion instead (the large literal against the
  `Cons` chain); the per-piece form does not build that literal.
- **What a column means is a corollary, not a premise.** `{p}_column{j}_means`
  says the count slot `j` holds is `word_of_nat(64, column_means(columns, j)(input))`,
  from the bundle's `computes`. `{p}_stdout` is still stated over the
  state's counts (`command_stdout`); restating it over the columns' meanings
  is residue (§11).
- **Two refusal controls at source** in the CLI test: a column that claims
  another column's meaning, and a column that counts another column's
  field. Each is refused at its own source line before anything is
  published.

### 10.1 Verification items, cheap and first

If one refutes the design, stop and amend it before working around it.

- **V1. `rest` and `frame` in `IoMemory`.** Add both fields, with `io_read`
  falling through to `rest`. How many existing proofs need more than the
  extra quantified argument? The expectation is only the `io_read` case
  lemmas (`io_read_stored`, the file-window lemmas). If the filter's process
  proofs need real edits, the fallback is a separate `ArgMemory` that embeds
  `IoMemory`, with the filter's pieces lifted through a frame law.
  **Holds, with the fields in the image (2026-10-04, §10's C1 status).**
  Existing proofs needed the extra arguments, `Inl` around their page
  writability, and one bound passed to `store_at_offset`.
- **V2. `WordLoad`.** Encode, decode and execute `MOV RAX, [RBX]`. Its
  `ExecuteBlock` and data-read facts follow the `ByteLoad` pattern, and
  reading eight bytes little-endian gives the word.
  **Holds (2026-10-04, C1).**
- **V3. A NUL scan over `ArgvAt`.** Prove a `ByteLoad` loop that finds a
  string's length at an open address in `rest`. This is the first data read
  whose address is not bounded by the page. It sizes C2's argument scan.
- **V4. `eof_run` with fd and failure continuation.** Make the change and
  recheck `elf64_read_filter` and its tests. The counters on
  `read_filter_process` should not move beyond the new parameter.
  **Holds (2026-10-04).** `eof_run(fd, body, ended, failed, …)`: every read
  event carries `fd`, and a failed read goes on as `failed(seen, errno)`.
  The driver `eof_from` takes the continuation as a fifth process
  obligation, `EofProcess.fails` (`EofReadFails`: from the failure tail with
  the errno in RAX), and its layout needs only the EINTR half of a tail
  (`RetryTail`), so a command can put its own code after the JZ. The filter
  supplies `read_exits()` and `tail_exits` and keeps its trace. The head
  still reads fd 0: a head that loads the fd from the frame waits on
  `WordLoad` (C1). On a cold `build-x86` of `wc` the binary is the same, and
  every counter of the formatter, the step piece and the program's own
  proofs is identical. All the change is library, paid once per image
  store: `eof_from` +23% steps (the failed read is now its own branch),
  `elf64_read_pieces` +7.7%, `elf64_read_filter` +0.02%, the whole build
  +0.11% steps and +4 items.
- **V5. One digit of the formatter.** One `emit` iteration with its table
  read and store, checked at an open place value. Compare its cost per
  declaration with `elf64_write_loop`'s, which is §9.3's analogue.
  **Holds, at the top of its band (2026-10-04).**
  `probes/wc_command/digit_emit.hthr`: from n < 10 · place in RDX and the
  place in RBX, `CMP; JB` out, `SUB; ADD` and `JMP` back, then `'0' + d`
  stored at the cursor, which steps past it, at an open place and an open
  cursor in the page. The table read is left out (it is one `WordLoad`,
  V2's). It checks as 57 items, about 2.2× the module time of
  `elf64_write_loop` (75 items), so about 3× per item, at one kernel
  worker; the loop's induction (`digit_loop`) is two thirds of it. So one
  of §9.3's seven loops costs about 1.5 points of today's cold build, the
  top of the 6–10 point band, before its table read and the place loop
  around it. If every loop costs that much, the loops come to about 10–12
  points instead of 6–10, and the cold build stays under today's even with
  the driver at twice its estimate. Two proof costs to plan for: `omega`
  inside the long proof bodies needs its arithmetic as small top-level
  theorems, and `bv_omega` does not read `sign_extend`, so an `AddRI8`
  immediate's value is a `refl` lemma.
- **V6. The stat bytes.** `stat_regular` and `stat_size` as functions of a
  144-byte list. Check that `WordLoad` at offset 24, `AND 0xF000` and a
  compare against `0x8000` decide `stat_regular`, at an open `st`.

## 11. Decisions taken here, and residue

Taken by default in this round (to revisit if the user disagrees):

1. **GNU's output, width rule included**, not POSIX `%d %d %d`. Matching
   the host is what the tests check. POSIX `%d` is the width-1 case of the
   same formatter, so nothing is lost. It costs one syscall, `newfstatat`.
2. **No stderr diagnostics.** Exit status only, as for `wc -l`.
3. **Exit at once on a failed write.**
4. **The flags are `-l -w -m -c`.** `-m` is nearly free: in the C locale it
   is the byte count in its own column.
5. **The formatter is library code**, not generated.
6. **`Fields` goes when `wc` migrates**, as F5 deleted the old processes
   once their last client moved. It takes the generated `%7d` certificates
   out of every cold build and out of the suite. Whether
   `field_low_certifies` and `field_high_certifies` stay on as generator
   coverage is the user's call: they are the structured generator's largest
   inputs, and also among the suite's heavier tests.

Residue, filed as `issues/native-wc-command-residue.md`: stderr
diagnostics (`strerror`, `quotef`), long options, `-L` (a max-line-length
fold; the step can carry it), `--files0-from`, `--total=`, names with
newlines quoted, and continuing after a failed write. `fields-profile-shape`
is superseded once C4 lands, since the row loop prints any subset of
columns.

## 12. Not this round

- **One program logic over interaction trees**
  (`issues/native-one-program-logic.md`). The command's claim becomes a
  lemma of it later, as the filter's does.
- **`tr` with sets from argv.** argv lands here. `tr`'s sets as data read at
  run time are a different step (a table lookup, not a fixed comparison),
  so that is its own round.
- **Locales and multibyte `-m`.**
- **Expanding filters** (`issues/native-expanding-filters.md`).
