# Rung 2: spans of anything, a span that grows, and memory a function owns

Status: **design, 2026-11-24**, for Minus's review. Asked for as "the
missing parts for memory, so that runtime programs can start allocating
vectors and we can design hashmaps". It is step 6 of
`docs/native/dogfooding-plan.md` §7 (the design note rung 2 opens with) and
extends `docs/native/span-record-design.md` (`Bytes(n)`),
`docs/native/layout-design.md` §9 (functions of a laid record) and
`docs/native/native-heap-arena-design.md` (the builder's arena). It changes
no principle of `docs/compilation-vision.md`: a buffer is a value in every
meaning, addresses appear only where a level is tied to the machine (§2.5).
§10 lists what Minus decides.

## 0. Recommendation

- **A fixed-capacity hash table compiles today.** A word map in one laid
  record (keys and values side by side, a Fibonacci slot, linear probing)
  and a byte set over a lent `Bytes(n)` are compiled `runtime fn`s with
  their agreement published and runs by `refl` (the ledger,
  `lib/_tests/native/runtime/runtime_ports_tests.hthr`, "a hash table of
  fixed capacity"). What stops it being *written* the natural way is a
  short list of surface gaps (§2), each now pinned by a ledger row.
- **A span of elements with a run-time count is a record and a second
  meaning, not new code.** The codec accessor class already reads and
  writes an element at a base and count that are words
  (`Accessor::read_at`/`write_at`, `stored_accessor.hthr`). What is
  missing is `Span<A>(n)`, the analogue of `Bytes(n)` for any element with
  an accessor, and its meaning over the record (§3).
- **A vector is a span with a fill mark**, and pushing past its capacity is
  an outcome the function answers, never a precondition (§4).
- **Memory a function owns is an arena inside its one written span.** The
  arena's top is a field of a header at the span's start; an allocation is a
  window `(base, count)`; growing a vector is allocating a larger window and
  copying within the same span. The compiler's theorem needs nothing new:
  it is all one span (§5). Exhaustion is an answer (`Full`), and a caller
  that can (Rust, through an export) lends a larger span and calls again.
- **Several written spans wait for a customer one span cannot serve** (§6).
- **A hash map's correctness is a theorem about the Heather function**, not
  a `datarepr`: the `runtime fn` *is* the function the agreement certifies,
  so "it refines a finite map" is proved over the function directly, against
  `assoc.hthr`'s laws (§7).
- `mmap`, frees of single windows and metered bounds stay where they are
  filed (`native-arena-mmap`, `nh-ownership`, `memory-bound-certificates`).

## 1. What memory a `runtime fn` has

As of this note:

| What | Where | Size fixed by |
|---|---|---|
| A byte span with its length, `Bytes(n)`, read and stored at a found index | `bytes.hthr`, `rt_bytes.hthr`, `rt_bytes_loop.hthr` | the caller (`n` is a word) |
| A laid record over a span, its word fields and arrays of words indexed by a word | `laid.hthr`, `rt_held*.hthr`, `stored_words.hthr` | the type (an array's count is a literal) |
| Spans only read, besides the one written | `runtime-loop-over-several-spans` (closed) | the caller |
| A window of a span lent to a callee | `FTm::Lend`, `function_ir_lower_views.hthr` | the lender |
| The builder's arena of write-once line cells | `native_arena.hthr`, `native_build_arena.hthr` | the program's buffer |

and what it does not have: a span of anything but bytes with a run-time
count (an array parameter `[u64; n]` "has no runtime layout"), more than
one *written* span (`rt_file.hthr`: "a computation writes one span, span 0
of its file"), and any way to obtain memory (the Linux model's calls are
`read`, `write`, `open`, `close` and `stat`). `rt::Ty::Lines` and
`ConsLine` exist, but the lowering refuses them (`runtime-fn-arena-lists`).

`import runtime_data;` is the one import a function of a span or a laid
record needs (`lib/native/runtime/runtime_data.hthr`, this round): the
generator cites the span and record meanings by qualified name, and those
modules cannot sit under `runtime`, since the codecs' accessors are written
with `runtime fn`.

## 2. What the hash table rows showed

Written as a newcomer writes them, each refused (the ledger rows):

| Shape | Refusal | Owner |
|---|---|---|
| a lookup loop that only reads the record, or a reader of a `Bytes(n)` answering a word | "a loop that only reads the record is not taken yet"; "a function over a span returns `Mutated<…>`" | built 2026-11-24: a reader publishes the writer's statement at the record unchanged (`HWorld::unchanged`), loops included (`layout-design` §9.5, `span-record-design`); a reader loop that calls is left (`runtime-record-function-limits`) |
| the slot as `k % cap` | `bv_omega` reads `urem` as an atom, so `k % 4 < 4` is not found | built 2026-11-24: `x % c < c` at a literal, `x % n < n` under `0 < n` or `n ≠ 0`, the quotient's bounds (`bv-omega-word-remainder-quotient`); a mask (`k.band(3)`) and a shift of the top bits were found before |
| the insert as a `while` whose measure is assigned in its arms | "must decrease the measure": the search did not split the `if` | built 2026-11-24: the decreases closer splits a stuck `if` and searches each arm (`while-decrease-through-branches`, closed); the row now stops at the generator (its loop's state has no runtime layout) |
| a store under an `if` with code after it | "the span through a branch that joins again" | the loop combinator rebuild (`loops-on-one-combinator`), dogfooding plan §5.3b |
| `break` or `return` in a `for` (stop at the found slot) | "has no `break`, `continue` or `return` yet" | `loops-on-one-combinator` |
| a span function that ends in a call of another | "ends in `Mutated(span, value)`…"; binding the call first works | `runtime-record-function-limits` |
| a `u8` key beside the span | "takes and returns 64-bit words for now" | `runtime-repr-narrow-words` |
| a table as a parameter, `mut t: [u64; 8]` | "a type with no runtime layout" | §3 |

None of these is about memory. They are rung 1 and the generator's
coverage, and they are what a port meets first. The first two rows were
closed in the round that wrote this note, and the third's elaborator half; the table keeps them so the
ledger's history reads.

## 3. A span of elements: `Span<A>(n)`

```heather
record Span<A>(n: u64) { items: List<A>, sized: items.len() = n.toNat() }
fn Span::len<A>({n: u64}, self s: Span<A>(n)) → u64 { n }
fn Span::at<A>({n}, self s: Span<A>(n), i: u64, inside: ∥i < s.len()∥ := bv_omega) → A
fn Span::put<A>({n}, self s: Span<A>(n), i: u64, a: A, inside: ∥i < s.len()∥ := bv_omega) → Span<A>(n)
```

The same decisions as `Bytes(n)` (span-record-design): the count is in the
type, `sized` is a plain field so `n` is inferred, `s[i]` is `s.at(i)` and
`s[i] := e` is `s := s.put(i, e)`, and an index takes a found proof.

**Its meaning is held, not threaded.** `Bytes(n)` holds its bytes, and
`FTm::over` threads them by conversion. A span of `A` holds values, and the
bytes hold them by the element codec: the span's bytes are
`codec.put` of each item at `i * stride`. That is `rt_held`'s shape (a
record the span holds, `Stored::Holds`), with the record's array field
replaced by a list whose count is the word `n`. So the second meaning is
`FTm::held` at a codec of a run-time-counted array, and its leaf cases are
the accessor's laws at an open base and count, which the class already
states (`reads_at`, `writes_at`, `reads_past`, `writes_past`). What is new
is one codec, "`n` items of `c`" with `n` a word (`Stored::array` takes a
`Nat` the type fixes), and its holds relation.

**What it costs in the code.** An element's offset is `i * stride + base`.
A stride that is a power of two is a shift; otherwise it is the multiply
row (`Operation::Mul`). The accessor's own test of `i` against the count is
taken on every access today and is never false where a proof was found;
dropping it is `layout-design` §9.5's next step and applies here unchanged.

**Naming.** The dogfooding plan says `Words(n)`. `Words` is already a type
function in `rt_io_program.hthr` (a curried function of `k` words), and the
element is not always a word: a span of a laid record (a token, a hash
table's entry `{key, value}`) is the same construction at a record's codec.
So: `Span<A>(n)`, with `Span<u64>(n)` for words. `Bytes(n)` stays as it is
(`u8` has no accessor, and its meaning by conversion is cheaper); whether it
becomes `Span<u8>(n)` is a later cleanup.

**Customers.** `numeral`'s limbs (`port_pred_limbs`, ledger row 11), the
token array, and the hash table with a run-time capacity.

## 4. A span that grows: the fill mark

```heather
laid record Filled<A>(cap: u64) { len: u64, items: Span<A>(cap) }   // illustrative
```

A vector of capacity `cap` is a span of `cap` items and a word `len ≤ cap`.
Its meaning is the first `len` items, a `List<A>`:

- `get(i)` takes `i < len`, found as every index is;
- `push(x)` stores at `len` and increments it when `len < cap`, and
  otherwise answers `Full` and leaves the vector as it was. That is
  `datarepr-design` §1.3's FINDING 1: construction is where finiteness
  bites, so the outcome is part of the answer, never a precondition an
  argument could discharge;
- `pop`, `truncate`, `clear` change only `len`.

Laid as one record, the fill mark and the items sit in the one span the
function writes, so a function of a vector is a function of a laid record
today, with `items` an array whose count is the word `cap` (§3).

## 5. Memory a function owns: an arena in its one span

Spellings in this section are illustrative.

A vector that grows past its capacity needs memory it was not lent at that
size. The cheapest route that keeps the compiler's theorem unchanged is to
make allocation a function *of the span*:

```heather
laid record Arena { top: u64, limit: u64 }   // at the span's start; the rest is the heap
record Window { base: u64, count: u64 }       // a region of the heap, as two words

runtime fn Arena::alloc(mut self a: Arena, size: u64) → Outcome<u64>   // the base, or Full
```

- **Allocation** compares and adds: `top + size ≤ limit` gives `base := top;
  top := top + size`, otherwise `Full`. It is `native-heap-arena-design` §2's
  bump with the top a field of the span instead of a word the program keeps.
- **A vector in the arena** is a `Window` and a fill mark. Its items are at
  `base + i * stride`, which is exactly `Accessor::read_at(span, length,
  base, count, i)`.
- **Growing** allocates a window twice as large, copies the items with a
  loop over the one span (read at the old base, store at the new; no views
  are needed, it is one span), and answers the new window. The old window is
  left behind until the arena is reset.
- **Reset** is `top := mark` at a mark taken earlier: the region pattern,
  freeing everything allocated since. Freeing a single window is
  `nh-ownership`'s (§9).

**Why one span.** The function compiler's homes are already words (an
address and a length, carried by loops and handed on by calls), and the
meaning already threads the one written span's bytes (`FTm::sem`). An arena
inside it adds no level, no home and no machine reasoning: every program
over it is a program over one span, which the compiler proves today. The
rival, memory obtained from the system, needs a buffer reached through an
address in a word in the *program* compiler, the separating product of views
(`wp-view-separating-product`) and the permission change of
`byte-memory-design` §7. That is `native-arena-mmap`, for standalone
programs, and it can come later without changing any of this: the arena's
laws are about its bytes wherever they live.

**The laws, proved once in the library** (the line arena's `extend_abs` and
`cons_abs` generalised):

| Law | Statement | What it gives |
|---|---|---|
| `alloc_below` | allocation changes no byte below the old top | every window allocated before survives every later allocation |
| `alloc_fresh` | the window allocated is inside the heap and at or above the old top | a new window is disjoint from every older one, as numbers |
| `store_apart` | a store into window `W` changes no byte of a window disjoint from `W` | pushing to one vector leaves every other |
| `grow_abs` | after growing, the new window's first `len` items are the old window's | growing keeps the vector's meaning |

Disjointness is a comparison of two intervals of words, so it is decided
by evaluation or found by `bv_omega` where the windows are open, never
proved inside the compiler (vision §2.5's "geometry is decided where
addresses are numbers").

**Aliasing.** A `Window` is two words, so a program can copy one, and two
copies can then push into one window. The compiler's theorem is still
right (it is about bytes). What fails is the list-level statement "this
vector means the list it was built from" for the copy that did not push.
Under the default setup such theorems take the windows' disjointness as a
hypothesis, discharged per program by the laws above; under `nh-ownership`
the judgment discharges it once (the `Unique` fact,
`facts-on-demand-design` §7). The line arena avoids the question by writing
each cell once; a growing vector cannot.

**Exhaustion.** `Full` is an answer, not an exit: a function has no exit.
A Rust caller that receives it lends a larger span and calls again (an
export's contract states the answer; `native-library-exports-design`). A
`write-elf` program chooses what `Full` does, normally the "memory
exhausted" exit `native-heap-arena-design` §2 already gives its tools.

**The builder's line arena** becomes the special case: a line is a window
written once while it is the top (`open_cell`/`push`/`close_cell`), and its
`extend_abs` is `alloc_below`. `runtime-fn-arena-lists` (lists as arena
cells in `rt`) stays rung 3's: cells with a tag and pointers between them
are inductive data, and this note gives them their allocator.

## 6. Several written spans

`rt_file.hthr`'s computations write one span and read others; a call lends
windows of them (`FTm::Lend`), and two views of one buffer are lowered only
when the written one is the buffer's only view (`views-of-one-buffer-apart`).
A program statement lends its first buffers whole
(`statement-lends-named-buffers`).

Every customer in §3 to §7 fits one written span: a vector and a map
together are two windows of one arena. So rung 2 does not wait on two
written spans. They are wanted when a function is handed two buffers it did
not allocate and writes both (a `memcpy` between buffers its caller owns,
ledger row 15; a codec reading one image and writing another). Then the
meaning threads a list of spans, `put_views` puts back several windows, and
`Loan::view_written_reads` is stated for a set of windows: the third bullet
of `views-of-one-buffer-apart`. Four home words per two spans make register
pressure the first cost (`function-ir-values-in-kept-registers`).

## 7. The hash map

**Today** (the ledger rows): capacity fixed by the type, open addressing,
linear probing, 0 the empty key, a Fibonacci slot or a mask. Probing ends in
its own call with each arm its own `Mutated`; lookup is written as a
function that leaves the record (until readers land, §2).

**Its specification is a theorem about the function.** A `runtime fn` is
ordinary Heather, and its agreement says the code is that function. So
"this table is a finite map" is proved over `PortMap::insert` and
`PortMap::get_at` as Heather functions, against `assoc.hthr`'s laws
(`List::assoc_get_set_same`, `List::assoc_get_set_other`), with no
`datarepr` between:

- `abs(m)` is the association list of the occupied slots;
- `inv(m)` is the probing invariant: every key is reachable from its home
  slot without passing an empty one, keys are distinct, and
  `count` is the number of occupied slots;
- `insert` keeps `inv` and, on its success arm, means `assoc_set` up to
  lookup: at every key, `abs(insert(m, k, v)).assoc_get(i)` is
  `abs(m).assoc_set(k, v).assoc_get(i)`. Equality of the lists is the wrong
  statement, since `assoc_set` shadows by consing and a table holds one row
  per key in slot order. The full answer comes only when `count = cap`;
- `get` means `assoc_get` under `inv`.

The proofs are loops over a measure, so they are ordinary induction on
`left`. `datarepr` earns its place when generic code over `List` or a map
interface is to run on the table (transfer), which is rung 4's.

**With §3 and §5**: the table's slots are a `Span<Entry>(cap)` in a window
of the arena, and a full table (or a load factor reached) allocates a window
of twice the capacity and reinserts every entry, the old window left until
reset. Deletion takes tombstones or backward shifting; backward shifting
keeps the invariant above without a third slot state and is preferred.

**Keys that are byte strings** are windows of the arena; hashing one is a
read-only loop (FNV compiles today, ledger row "FNV-1a"), comparing two is a
read-only loop over two windows of one span, which is a reader (§2) and
needs no second written span.

**Generic `K`, `V`.** The table is generic in its entry's codec at
kerneltime, and the accessor class finds the code per codec, so one
`runtime fn` per instantiation is what the generator emits once generics by
specialisation exist (rung 4: an ordinary generic `fn` is refused today,
ledger row `port_bump_twice`). Until then a table is written per key and
value type.

## 8. Order of work

Each step lands its ledger rows; none needs a decision beyond §10's.

1. **The surface gaps of §2** that rung 1 does not already own: readers,
   the remainder's bound and the `while` decrease (all three built
   2026-11-24).
2. **`Span<A>(n)`** (§3): the codec of a run-time count, its holds
   relation, the reflector's reading of `s[i]` on it, the generator's
   `runs_held` at it. Customer: `numeral`'s limbs. Issue `runtime-span-of-codec`.
3. **The fill mark** (§4) as a laid record over 2; push answers `Full`.
   Customer: the token array.
4. **The arena** (§5): `Arena`, `alloc`, `reset`, the four laws, the growing
   vector over 2 and 3. Issue `runtime-arena-in-span`.
5. **The hash map's specification** (§7), first at fixed capacity over the
   ledger's table, then rehashing over 4. Issue `runtime-hash-map-spec`.
6. Two written spans (§6) when a customer needs them.

Steps 2 and 5's first half are independent and can run in parallel.

## 9. What this does not do

- No `mmap` (`native-arena-mmap`), no free of a single window, no garbage
  collection: one arena, reset whole or to a mark.
- No allocation bound as a theorem (`memory-bound-certificates`); a
  program's arena size is chosen by its caller.
- No change to `Source`, FunctionIR, the lowering or
  `native_compile_correct`.
- No `datarepr` declaration; `datarepr-guarded-images` stays the route for
  the arena's representations when transfer wants them.

## 10. Questions for Minus

1. **Exhaustion as an answer.** `Full` is returned, and a caller that can
   retry lends more (§5). Recommended: yes; the alternative, an exit, exists
   only for programs.
2. **The arena in the written span** rather than memory from the system
   first (§5). Recommended: yes; `mmap` keeps its issue for standalone
   programs.
3. **`Span<A>(n)` as the name** for rung 2's "spans of anything" in place
   of `Words(n)` (§3). Recommended: yes.
4. **Hash map correctness as theorems about the function**, against
   `assoc`, before any `datarepr` (§7). Recommended: yes.
