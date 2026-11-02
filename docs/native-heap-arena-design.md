# The native heap: a bump arena — design

Status: **proposed 2026-11-02**, landing with its first slice. Owner:
`issues/native-heap-arena.md` (milestone `nh-heap`, round R9 of
`docs/compiler-milestones-proposal.md`, §4.2 N4). It reads
`docs/compilation-vision.md` first, as every compilation round does, and
extends `docs/datarepr-design.md` (§1.3, FINDING 1) with the first
representation whose constructor images are guarded.

The issue asks for a short design section before anything runs: a bump
arena in the data segment, then `mmap` as a Linux event, exhaustion as a
defined exit, and `datarepr` cells for `List` and small trees. It also asks
whether the arena needs the separating footprints of
`issues/wp-view-separating-product.md` before anything runs, and to stop if
it does. It does not (§1).

## 0. Recommendation

- **An arena is a `Source` buffer and a word.** The buffer is the arena's
  bytes, in the data segment like every buffer; the word is its top, the
  count of bytes used. Allocation compares and adds; a cell's fields are
  byte stores and loads. Nothing in `Source`, its meaning, the compiler or
  `native_compile_correct` changes: an arena program is a program the
  compiler already proves (§1).
- **Running out is a defined exit.** An allocation that does not fit runs a
  statement the program gives, which exits (GNU's tools say "memory
  exhausted" and fail). It is a `Branch` on a comparison in the source, so
  the meaning has the exit in it, and the machine meets it exactly (§2).
- **Cells are written once.** A cell is written while it is the arena's
  top and never again; a list is grown by consing, never changed in place.
  That is the default setup's discipline: it copies where it would update
  (`compiler-milestones-proposal` §4.3). Updating cells in place, and
  freeing them, is what `nh-ownership` will give the compiler (§6).
- **The representation is a `datarepr` repr with guarded images.** A list
  is an `ArenaRef`, the arena's bytes and the name of its first cell; its
  meaning is read off the bytes (`ArenaRef::abs`), its invariant is that
  every cell names a cell below it and lies within the bytes
  (`ArenaRef::inv`). Two laws carry everything: growing the arena keeps
  every list in it (`extend_abs`), and consing is the cell and then the list
  while the arena is within its limit (`cons_abs`). Both are proved, once,
  in `lib/native/native_arena.hthr` (§4).
- **`mmap` comes later, as a Linux event.** A fixed arena in the data
  segment is enough for `tac` and `sort`; growing one by `mmap` adds a call
  to `LinuxCmd` and a statement to `Source`, and changes only where the
  bytes live (§5).
- **"Ordinary Heather" waits on N1 and N3.** The done-when asks for `sort`
  and `tac` written as ordinary Heather. The `runtime fn` front end lowers
  only words today (R5b, `lib/native/runtime/rt_lower.hthr`), and I/O as
  capabilities is R6 (`effects-uniqueness-surface`), still open. So this
  round writes both tools with the builder, as `grep -F` was for
  procedures, over the arena they will lower to, and leaves the front-end
  half to the `rt` rounds with the representation ready for them (§3, §7).

## 1. Where the arena lives, and why no footprints are needed

A `Source`'s buffers are already disjoint: `Env.buffers` is a list of byte
lists, a byte node names its buffer, and the compiler gives each buffer its
own range of the data segment (`Layout`, `DataRegion::process_data`), with
`native_compile_correct` relating each to its list. A store into one buffer
cannot reach another, and that is proved once, for every source.

An arena is one more buffer, so it inherits all of that. The separating
product of `wp-view-separating-product` composes two `Wp` views over
disjoint regions of machine memory; it is what a *proof about x86 code*
needs when one view knows the page and another the frame. Nothing here
reasons about x86 code. The arena's reasoning (§4) is about the bytes the
source's meaning holds, a `List<BitVec(8)>`, and the compiler's theorem
already moves every such fact to the machine. So the arena needs no
footprints before anything runs, and the issue's stop condition does not
fire.

Where footprints would enter: a separately mapped arena (§5) is a second
region of machine memory that the compiled code reaches by address, and
the compiler's theorem would then speak of two regions at once. That is the
`mmap` round's question, not this one's.

The arena's size is the buffer's capacity, fixed in the source. The data
segment holds at most `io_data_limit()` (1 GiB), so a cell's name and a
payload's length fit in four bytes; `arena_limit()` is that limit, and the
representation's laws assume it (§4).

## 2. Allocation and exhaustion

A cell is named by its offset plus one, so the name 0 is no cell and is the
empty list. Allocating `size` bytes is

```
if capacity - top < size then full else { cell := top + 1; top := top + size }
```

where `full` is a statement the program gives (`Arena::open_cell` with
`size` 8, a cell's header, `lib/native/native_build_arena.hthr`). A byte pushed onto the open cell is
the same with `size` 1 (`Arena::push`), which is how a line of any length
is read straight into its cell.

Exhaustion is a **defined exit**, not a fault: the source's meaning
branches to `full`, and `full` exits with the status the program chose.
This is the same choice `nh-procedures` made for calls nested past the
depth (`call_depth_status`, `docs/native-procedures-design.md` §2): the
limit is part of the meaning, so a machine with a finite arena meets it
exactly, and the theorem is partial correctness with the exit as one of
the outcomes. It is also `datarepr`'s policy for machine-state partiality
(`docs/datarepr-design.md` §2): running out of memory is an outcome the
operation carries, never a precondition an argument could discharge.

A metered bound, a theorem that some program never reaches `full` on
inputs below a size, is `memory-bound-certificates`' follow-up, as the
issue says.

## 3. The builder's arena, and the tools

`native_build_arena` gives builder tools an `Arena`: the buffer, its top
word, the name the next cell would get, and the length of the open cell's
payload so far. A line is consed by opening a cell onto the list read so far
(its header: the list's name and a zero length), pushing the line's bytes as
they arrive, and closing it (writing its length). The cell is the arena's
top from its opening to its closing, so it is written only while it is the
top.

Writing a name or a length means writing its bytes, and the compiler takes
no shift yet (`function-ir-x86-shift-legalization`). Cutting a byte out of a
word by testing its bits works, but costs: unrolled, the tests made
`write-elf`'s fork run out of memory; as a counted loop, the loop's one
leaf was past a declaration's fuel. So the arena keeps the numbers it writes
as their bytes all along (`Name`): the next name and the open length are
counted up with a carry as they grow, and the list's name is a copy of the
next name taken when a cell opens onto it. No word holds a name beside its
bytes: a word a loop updates stays live across the loop, and the live words
are what the certificate pays for (§3.1), so the list's head is kept as a
word from the top when its cell opens, and nothing else needs one.
Reading a name back needs no shift: the high byte, doubled eight times in a
small loop, plus the next, and so on. Names have three bytes, enough for an
arena up to 16 MiB; the fourth is written zero. When the compiler takes
shifts, `Name` can go and a name is a word again.

A walk over a list reads no length back at all. A list grown by consing at
the top lies in the arena newest first and cell against cell, so a cell's
payload ends where the cell before it in the list starts, and the first
cell's at the top: `Arena::each` hands its body each payload's length from
where the walk has been. The length is still written in the cell, where
`native_arena`'s layout has it, for any reader that comes at a cell
without walking to it.

`lib/native/native_heap_tools.hthr` writes both customers over it:

- **`tac`** reads its input into a list of lines, each with its newline;
  the list's first cell is the last line, so writing the list in order is
  the input reversed. GNU's handling of a last line without a newline
  (written first, as it is) falls out of keeping the newline in the cell.
- **`sort`** reads its lines without their newlines into the same list,
  then writes them in order without changing the list: each pass over the
  list finds the least line after the one last written, in the order of
  the lines' bytes and then of their cells, so lines that are alike are
  each written once. That is quadratic in the number of lines, like an
  insertion sort, and it keeps the arena write-once. The pass keeps the
  lengths of the line last written and of the best so far beside their
  cells, so comparing two lines reads only their bytes. The order is
  inlined at its two sites: a tool with procedures is still lowered whole
  by `write-elf` (`native-procedures-write-elf-capacity`), which these
  tools are past.

Both run out of arena with GNU's message and GNU's failing status (1 for
`tac`, 2 for `sort`), and the tests check that exit beside GNU's output on
inputs that fit (`crates/cli/tests/native_tools.rs`).

These tools are not proved against GNU's behaviour, as no builder tool is
(`native_tools`, `grep_f`): the certificate is that the binary does what
the source says, and the GNU tests check that the source says what GNU
does. Nor is the builder's arena code proved to write `native_arena`'s
layout: the builder has no semantics of its own beyond the source it
lowers to. Tying the two is the front end's job (§7).

### 3.1 What `write-elf` needed

Both tools are larger than the corpus's, and `write-elf`'s certificate ran
out of one declaration's fuel on them: each part's live-out set was spelled
from its parent's (`{p}_o_{id}`), so every declaration that read one worked
the sets out again from the root, down every enclosing loop. `write-elf`
now reads each part's set on the fork and states it as a literal
(`emission::live_literals`); the joins between parts compare a part's
literal with its spelling over its parent's literal, one step down the
tree, so no declaration walks from the root. The kernel checks the same
statements as before.

What is left is the join's own comparison: a `Then`'s first part runs with
its sibling's live-in set live after it, so the join works out that set
over the whole sibling, which inside a loop is the rest of the loop's body.
Liveness costs about the statements times the square of the live set (each
step is a union or a difference of lists), and a whole part's emission
grows with the live set too, so a loop body's size and the words live
across it are what bound a tool: `sort`'s pass, with two inlined
comparisons each reading two lengths back by doubling, was past a
declaration's fuel at one join until the walk gave the lengths (above).
Stating each part's live-in set as a theorem its parent's joins rewrite
with, as the live-out sets now are literals, would make a join's cost one
step of liveness instead of a subtree's; that is issue
`native-write-elf-join-liveness`.

## 4. The representation (`lib/native/native_arena.hthr`)

The layout of a list-of-byte-strings cell at offset `o`:

```
o:       next cell's name (4 bytes)   payload length L (4 bytes)   payload (L bytes)
```

An `ArenaRef { bytes, at }` is the arena's bytes and a name. Its meaning is
read off the bytes, cell by cell, the name serving as fuel (each cell names
a cell below it, so a list of `k` cells is read in at most its name's
steps):

```heather
fn ArenaRef::abs(self r: ArenaRef) → List<List<BitVec(8)>> { arena_lines(r.bytes, r.at, r.at) }
fn ArenaRef::inv(self r: ArenaRef) → Type { arena_cells(r.bytes, r.at, r.at) }
fn ArenaRef::cons(self r: ArenaRef, line: List<BitVec(8)>) → ArenaRef {
    ArenaRef(r.bytes ++ cell_bytes(r.at, line), Succ(r.bytes.len()))
}
```

and the laws, proved by induction on the fuel:

| law | statement | why it is the one that matters |
|---|---|---|
| `nil_abs` | `ArenaRef::nil(bytes)` (the name 0) means `Nil` in any arena | the empty list costs nothing |
| `extend_abs` | `inv(r)` ⇒ `ArenaRef(r.bytes ++ more, r.at)` keeps `inv` and means `abs(r)` | the arena grows only at its top, so every list in it survives every later allocation: one arena holds many lists |
| `cons_abs` | `inv(r)`, `r.bytes.len() + 8 + line.len() ≤ arena_limit()` ⇒ `cons(r, line)` keeps `inv` and means `Cons(line, abs(r))` | the constructor image, on the allocation's success arm |

`extend_abs` is what makes a bump arena simple. A program conses onto a list
it built earlier, with other cells allocated in between; the list is then
`ArenaRef(current bytes, its name)`, and `extend_abs` says it still means
what it meant, so `cons_abs` applies at the current top. Consumption is
total, as FINDING 1 says it always is (`abs` and `inv` need no capacity);
construction carries the capacity.

### 4.1 Why not the `datarepr` form yet

The v1 `datarepr` declaration (`crates/elab/src/datarepr.rs`) takes total
images and unguarded laws: `mk_Cons : A → R → R` with `Cons_abs` and
`Cons_inv` under `inv` alone. The arena's `cons` is total as a function
(`ArenaRef::cons` is defined everywhere), but `inv` of its result needs the
capacity, and no `inv` can carry it: consing onto a list that satisfies
any `inv` can still overflow the limit. That is FINDING 1 exactly
(`docs/datarepr-design.md` §1.3: "construction is where machine finiteness
bites"), and the design's answer is the success-arm law, which the form
does not yet express. So the laws are theorems here, in the shape a
guarded image will have, and `issues/datarepr-guarded-images.md` is filed
for the form to accept them. Nothing about the representation changes
when it does.

### 4.2 Element types, and trees

The cell's payload is a byte string, which is what `tac` and `sort` hold.
A list of another element type is the same cell with the element's
encoding as the payload; the laws then need the encoding's round trip
(`decode(encode(x) ++ rest) = x`), which is the one place `read_arena_word`
is used here. A binary tree is a cell with two names and a payload, and
the same two laws (extension and the node image) with two recursive reads;
its order argument is the same (both children are below the node). Both
are filed as `issues/native-arena-cell-codecs.md`, to land with the first
customer that holds anything but lines.

## 5. `mmap`

A fixed arena is sized when the program is written. Growing one at run time
is a Linux call: `mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)`,
a new `LinuxCmd` in `lib/std/os/linux/linux_calls.hthr`, a `CallShape` in
`Source`, and a region the compiled code reaches through the address in a
word, not through a fixed offset in the data segment. That last part is
new to the compiler: today every buffer is at an address the layout fixes.
It is where the separating product (§1) and `byte-memory-model`'s permission
changes (`docs/byte-memory-design.md` §7) come in, so it is a round of its
own (`issues/native-arena-mmap.md`), and nothing in §2–§4 depends on it:
the representation reads the arena's bytes wherever they live.

## 6. What `nh-ownership` adds

Under the default setup a cell is written once. A program that wants to
update a cell (relink a list, bump a counter in a tree node) must copy the
path to it. The ownership setup's judgment (`docs/compiler-milestones-proposal.md`
§4.3, `issues/ownership-discipline-over-code.md`) is what lets the compiler
update in place: a cell reached only through a unique reference may be
rewritten, and its soundness theorem is what keeps `extend_abs`'s
guarantee for every other list. Frees (resetting the top below cells no
list reaches) are the same judgment's. This round keeps to write-once so
that the default setup's laws are the whole story.

## 7. The front-end half

`docs/runtime-fn-setups-design.md` §8 records what N4 adds to `rt`: a type
`Repr(spec, repr)` laid out as a cell name, its meaning the spec type
through `abs`. With this round that becomes concrete:

- `rt::Ty` gains a list-of-bytes type laid out as an arena name, `Ty::Holds`
  at it saying the port holds a name `at` with
  `ArenaRef(arena bytes, at).inv()` and `abs` the value.
- `Cons` in a runtime fn lowers to `open_cell`/`push`/`close_cell`'s region,
  and its case of `Tm::lower_sound` is `cons_abs` (on the success arm) and
  `extend_abs` (for every other live list); `Nil` is the name 0
  (`nil_abs`); a `match` on a list reads the cell's header.
- Allocation's failure arm is an exit, so the lowering needs N3's `Source`
  statements, as `runtime-nat-checked-arithmetic`'s trap does.

That is `issues/runtime-fn-arena-lists.md`, after R6. Its done-when is the
one this issue started with: `sort` and `tac` as ordinary Heather.

### 7.1 What the first front-end round built (2026-11-02)

The parts that do not wait on R6:

- **The customers, written.** `lib/native/runtime/line_tools.hthr` has
  `Io::tac` and `Io::sort` as ordinary Heather over `Io`: `let mut`, `for`
  over lists, statement `if` and `match`, and `mut self` reads and writes.
  Nothing in them recurses, so none needs procedures. The input is read
  into a `LineReader`, whose finished lines are consed last first, the
  order the arena holds them in. `tac` writes that list as it is. `sort`
  writes it in byte order by the builder's selection, one walk per line,
  with ties broken by place (`LinePick`). The list is only read, so the
  program allocates no cell after reading, and the arena stays write-once.
- **What the meaning leaves out.** The arena's capacity is not in the
  function. Running out is the lowered program's defined exit (§2), so the
  lowering's theorem will say "this function's outcome, or the exhaustion
  exit".
- **Checked against GNU's cases.** `line_tools_tests` states what the two
  write on the cases `native_tools.rs` runs against GNU: lines across
  reads, blank lines, a last line without a newline, lines alike, prefixes,
  bytes compared unsigned, and failing reads and writes. Each is a literal
  checked by `refl`. Reading the builder tools' sources against the same
  worlds fits one declaration's kernel fuel only at a single line, because
  building the source and running its arena code by conversion is past the
  fuel at two lines. So `tac` is checked against its builder source at one
  line and at no input, and the literals carry the rest.
- **`rt` has the code.** `Ty::Lines` is `List<List<BitVec(8)>>`. `Nil` is
  the literal `Lit(Lines, 0)` (the name 0), and `Cons` is the primitive
  `ConsLine(cap)`. `Fold` reads its element code from the list's code
  (`Ty::elem`, `Ty::items`), so one node folds both a byte buffer and a
  list of lines. The reflector reads `List<List<BitVec(8)>>` as `Lines` and
  the two constructors. It refuses `Cons` onto a byte buffer, since a
  buffer is written in place, and a list of anything else. Each of these
  pins by `refl` (`rt_tests`, among them `reversed`, which is `tac`'s list
  as a fold onto `Nil`). The lowering refuses `ConsLine`, and `Ty::Holds`
  at `Lines` is `False`, as it is at `Bytes`, until the arena lowering.

Left, in order:

1. **Ports.** `Ty::Holds` at `Lines` should say the port holds a name with
   `ArenaRef(arena bytes, at).inv()` and `abs` the value. The arena is a
   buffer, so this needs R6's lowering to `Source`: `StructuredRegion::eval`
   reads every buffer as empty.
2. **`ConsLine`'s case.** A cell copies the line's bytes from their buffer
   at the top, and running out exits. That is `cons_abs` on the success arm
   and `extend_abs` for every other live list.
3. **Matching on a list.** An elaborated `match` on a `List` is not a
   kernel `Case` the host presents. The reflector sees "a form the
   reflected fragment does not have", so `Arms` has to present recursive
   matches, or the reflector has to read the eliminator
   (`issues/runtime-reflect-list-match.md`).
4. **What the customers use that `rt` lacks.** `open ++ [c]` (a byte
   pushed onto the open line, which in the arena is a push onto the open
   cell); `for` with `break` or `return` (`List::for_in`); records with a
   list or buffer field; and `Io` itself (R6).
5. **Then** `runtime fn` on `Io::tac` and `Io::sort`, the GNU tests on the
   compiled binaries, and the builder versions deleted.

## 8. Slices

1. **This round.** The design (this note); the representation and its laws
   (`native_arena`); the builder's arena (`native_build_arena`); `tac` and
   `sort` over it, passing GNU's tests, and running out of arena as a
   defined exit (`native_heap_tools`, `crates/cli/tests/native_tools.rs`).
2. **`runtime-fn-arena-lists`**: the front-end half (§7), after R6.
3. **`native-arena-cell-codecs`**: other element types and trees (§4.2).
4. **`datarepr-guarded-images`**: the `datarepr` form accepts success-arm
   laws, and `native_arena`'s laws become a declared repr (§4.1).
5. **`native-arena-mmap`**: an arena grown by `mmap` (§5).
