# Layout as a library, and records laid over bytes

Status: **2026-11-12: layers 1 and 2 are built on PR #551, layer 3 is
begun, and layer 4 is design.**
Minus's direction (2026-11-12, the native thread): SHA-256's context goes
"straight to laid out fields, we're going to want them very soon
regardless", and "laying out should be something that's easy to use
relatively separately as well, similar to how Rust's layout api works …
so you can do it dynamically too for runtime layouting, etc. But ideally
better with proofs". Everything below that goes past those words is marked
**proposed**, and §7 lists the choices that are Minus's.

Owners of the seams: `issues/sha256-context-type.md` (the first customer),
`issues/rt-fixed-arrays-and-tables.md` (arrays of words in `rt`, byte order
as a codec), `issues/runtime-repr-narrow-words.md` (words narrower than
64 bits), `docs/datarepr-design.md` §5.2 ("layout is DATA": a programmatic
layouting value users can replace), `docs/compilation-vision.md` §2.4 and
§2.5 (representations; memory a function is lent).

## 1. What there is to build on

- **A span is a list of bytes and a length word**, lent to a `runtime fn`
  (`docs/native-one-compiler-design.md` §2.6). Reads are under the length
  (`byte_within`), stores too (`put_within`). No meaning mentions an
  address.
- **A window of a list is a lens** (`lib/std/data/list_window.hthr`):
  `window`, `put_window`, and the laws either way round, with what a store
  leaves before, inside and after it.
- **A word is its bytes in either order**
  (`lib/std/bitvec/bitvec_bytes.hthr`): `bytes_le`, `of_bytes_le`,
  `bytes_be`, `of_bytes_be` with both round trips, over `[BitVec(8); k]`.
- **A field path is a place** (`docs/sequencing-surface-design.md` §20):
  `ctx.count := ctx.count + n` and `ctx.block.put(…)` are ordinary
  Heather over a record.
- **`datarepr`** holds a spec type by a carrier with an abstraction
  function and transfers operations with certificates; today its carriers
  that run are single words (`SInt(64)`).

What is missing is the middle: nothing says where a field is, how wide it
is, or that two fields do not overlap, so `sha256_block.hthr` has `32`,
`64` and `320` in its bodies and the reader checks them against a comment.

## 2. The picture

Four layers, each usable without the ones above it.

1. **`Layout`**: a size and an alignment, as a value, with Rust's
   operations. Ordinary functions over `Nat`. This is what "easy to use
   relatively separately" asks for, and it has no opinion about records.
2. **A table of fields**: offsets and layouts, built by a rule (`repr(C)`
   order, or packed) or written by hand, with one checkable statement of
   what makes any such table sound.
3. **`Stored<A>`**: how a value of `A` is bytes of a layout: a reader, a
   writer and their laws. Words in either order, arrays, and a record from
   its fields' codecs. A field of a stored record is then a lens into the
   bytes, and the laws a program needs (a field reads what was put, and a
   store into one field leaves the others) follow once from layer 2's
   soundness and the window laws.
4. **A record declared laid out**, whose table, codec and accessors are
   generated, and which a `runtime fn` holds in a span it is lent.

Layers 1 to 3 are a library with no compiler in it. Layer 4 is a generator
over that library and then the runtime generator's work, and its design is
§5 and §6.

## 3. Layer 1: `Layout`

**Built** (`lib/std/machine/layout.hthr`, beside the byte memory model;
the rounding it stands on is `Nat`'s, in `lib/std/num/nat.hthr`):

```heather
// How many bytes a value takes and what its place is a multiple of.
record Layout { size: Nat, align_log: Nat }
fn Layout::align(self l: Layout) → Nat { (2).pow(l.align_log) }

fn Layout::bytes(n: Nat) → Layout { Layout(n, 0) }
fn Layout::word(k: Nat) → Layout { Layout((2).pow(k), k) }        // u8, u16, u32, u64 at 0, 1, 2, 3
fn Layout::Aligned(self l: Layout, at: Nat) → Type { l.align().Divides(at) }

// Where a value of `next` goes after one of `l`, and the two together.
fn Layout::offset_of(self l: Layout, next: Layout) → Nat { l.size.round_up(next.align()) }
fn Layout::extend(self l: Layout, next: Layout) → Layout {
    Layout(next.size + l.offset_of(next), l.align_log.max(next.align_log))
}

// The size rounded up to the alignment: what one element of an array takes.
fn Layout::stride(self l: Layout) → Nat { l.size.round_up(l.align()) }
fn Layout::pad_to_align(self l: Layout) → Layout { Layout(l.stride(), l.align_log) }
fn Layout::array(self l: Layout, n: Nat) → Layout { Layout(n * l.stride(), l.align_log) }
fn Layout::packed(self l: Layout) → Layout { Layout(l.size, 0) }
```

These are Rust's `Layout::new`, `extend` (which answers the pair of the
two functions here), `pad_to_align` and `repeat`. Two things differ, both
for the proofs:

- **The alignment is held by its exponent.** Rust checks at run time that
  an alignment is a power of two and every operation's documentation
  assumes it. Here it is one by construction, so no theorem carries a
  validity premise and `extend`'s alignment is a `max` of exponents, which
  each of the two alignments divides (`Nat::pow_dvd_pow_of_le`). Rust's own
  `ptr::Alignment` is the same idea as a type. The cost is that
  `Layout::word(2)` is the four-byte word; §7 item 6.
- **Rounding is `Nat::round_up`**, with `Nat::padding` under it
  (`n.padding(a)` is `(a - n.mod(a)).mod(a)`, Rust's
  `padding_needed_for`; `n.round_up(a)` is `n + n.padding(a)`). Both are
  total, and defined for any `a`, not powers of two only.

What Rust documents in prose is stated:

- `round_up` (in `nat.hthr`): the result is a multiple of `a`
  (`round_up_dvd`), at least `n` (`le_round_up`), less than `n + a`
  (`round_up_lt`), `n` itself where `n` already is one
  (`round_up_of_dvd`), the least such (`round_up_least`), idempotent and
  monotone. With them the divisibility facts `nat.hthr` lacked
  (`dvd_add`, `dvd_trans`, `dvd_mul_right`, `div_mul_of_dvd`).
- `offset_of`: at or past `l`'s end, aligned for `next`, and the first
  such place (`offset_of_ge`, `offset_of_aligned`, `offset_of_least`).
- `extend`: the first value is inside the pair and ends before the second
  begins; where the pair is aligned, each of the two is
  (`extend_aligned_l`, `extend_aligned_r`).
- `array`: element `i` ends at or before element `j` begins for `i < j`
  (`array_elements_apart`), every element is inside
  (`array_element_inside`), each is aligned where the array is
  (`array_element_aligned`), and an array needs no padding of its own
  (`array_stride`).
- `pad_to_align` once is enough (`pad_to_align_stride`); a word's stride
  is its size (`word_stride`).

Sums are written `size + offset`, the size first: `+` recurses on its
second argument, so an offset that is a successor steps by evaluation.
That is `list_window.hthr`'s convention, and a field's bytes are read
through its laws.

There is no overflow here because sizes are `Nat`. Where a layout is
computed by compiled code, §4 is the same functions over words.

## 4. Layouts at run time

A dynamic layout (an arena that carves records whose shape a program
computes, a length-prefixed message, a table sized by its input) needs
these functions as code. **Proposed:** each of §3's functions has a twin
over `u64` that is a `runtime fn`, with one theorem per twin: where the
`Nat` answer is below `2^64`, the word answer is its word. Rust returns a
`LayoutError` on overflow; here the caller holds the bound as a
hypothesis, or tests it with a comparison the path then knows, which is
how every other bound in compiled Heather is handled
(`docs/compilation-vision.md` §2.3). A function returns one word, so
`extend` is two functions at run time as it is in §3.

The first customer besides SHA-256 is the arena (`native_arena.hthr`),
whose cell is a record written by hand: the next cell's place at byte 0
and the payload's length at byte 4, each a little-endian word read by
`read_word`, and the payload from byte 8.

## 5. Layers 2 and 3: fields and what is stored in them

### 5.1 Layer 2, field tables

**Built**, in the same module:

```heather
record Field { offset: Nat, layout: Layout }
fn Field::end(self f: Field) → Nat { f.layout.size + f.offset }
fn Field::Apart(self f, g: Field) → Type { f.end() <= g.offset ∨ g.end() <= f.offset }

// Inside the whole, at an aligned offset, asking no more alignment than it gives.
fn Field::Within(self f: Field, whole: Layout) → Type { … }

// Any table, however it was made: each field within, no two sharing a byte.
fn Layout::Fits(self whole: Layout, fields: List<Field>) → Type { … }

// Rust's `repr(C)`: the fields in the order written, each at the next
// aligned place, the whole padded to its alignment.
fn Layout::in_order(items: List<Layout>) → Layout
fn Layout::fields_in_order(items: List<Layout>) → List<Field>
theorem Layout::in_order_fits(items: List<Layout>): Layout::in_order(items).Fits(Layout::fields_in_order(items))
```

- `in_order_fits` is proved once, for the rule, at any list of layouts
  (`fields_after_fit` is the statement from any start, which a rule that
  begins past a header would cite).
- A table written by hand (a wire format, a hardware register block, a
  layout chosen for a cache line) is checked by evaluation:
  `whole.fits_of_bit(fields, refl)`, over `Layout::fits_bit`. From there
  it is used exactly as a derived one. That is
  `docs/datarepr-design.md` §5.2's "an arcane hand layout proves the same
  obligations".
- What a sound table gives a client, by index: `fits_within` (field `i` is
  within the whole), `fits_apart` (fields at different indices share no
  byte), and `Field::within_aligned` (where the whole is aligned, the
  field is).
- Probes (`lib/_tests/std/machine/layout_tests.hthr`): a pair either way
  round, a record with padding, a register block written out of order with
  a gap, and four tables refused (bytes shared, an unaligned offset, a
  field past the end, a field more aligned than the whole). SHA-256's
  context computes there as `Layout(328, 3)` with its fields at 0, 32, 64
  and 320, which is what `sha256_block.hthr` has in its bodies by hand.

### 5.2 Layer 3, what is stored

**Begun** (`lib/std/machine/stored.hthr`): the record, `get` and `put`,
three laws and the codec of a byte. The codecs of words, arrays and
records are next and **proposed**.

```heather
// How an `A` is bytes.
record Stored<A> {
    layout: Layout,
    read: List<u8> → A,
    write: A → List<u8>,
    sized: (a: A) → write(a).len() = layout.size,
    round: (a: A) → read(write(a)) = a,
}

fn Stored::get<A>(self s: Stored<A>, bytes: List<u8>, at: Nat) → A { s.read(bytes.window(at, s.layout.size + at)) }
fn Stored::put<A>(self s: Stored<A>, bytes: List<u8>, at: Nat, a: A) → List<u8> { bytes.put_window(at, s.write(a)) }
```

- `Stored` values: `u8`; `u16`, `u32`, `u64` in each byte order (from
  `bitvec_bytes`, through a vector as a list); `Stored::array(n, element)`
  for `[A; n]`; and a record's from its fields'. Byte order is part of the
  codec and not of the type, as `rt-fixed-arrays-and-tables` asks: SHA-2
  is big-endian, ChaCha20 little-endian, and both hold a `u32`.
- The laws a program uses, each proved once for any codec: `get` after
  `put` at the same place is the value (`get_put`); `get` at one place
  after `put` at a place apart from it is unchanged (`get_put_apart`,
  whose premise is what `fits_apart` gives two fields); `put` keeps the
  length (`len_put`). These three are built, over two window laws added
  for them (`List::window_put_window_before`, `_after` in
  `list_window.hthr`); `get_put_fields` is the second stated of two
  fields. The fourth, `put` of what `get` read is the bytes,
  holds of a codec that uses every byte pattern (a word does, a `Bool` in
  a byte does not), so it is a law under a premise and not a field of the
  record.
- A reader that takes an unaligned or out-of-range offset is not
  undefined: `window` is total, and the laws carry the bound as a
  hypothesis.

Alignment matters for layers 1 and 2 (it is what `repr(C)` and an
allocator are about) and not for these laws, which are about bytes of a
list. It comes back where a machine load wants it (§6).

## 6. Layer 4: a record laid over a span

What the source should read as (**proposed**; the spelling is §7's):

```heather
laid record Sha256 {
    hash: [u32; 8] be,
    working: [u32; 8] be,
    block: [u32; 64] be,
    count: u64 be,
}

runtime fn Sha256::push(mut self ctx: Sha256, byte: u8) → u64 { … ctx.count := ctx.count + 1; … }
```

In two stages, because the first needs nothing new in the runtime
generator and the second is the generator's own round.

**Stage A: the declaration generates over the library.** A
declaration-prefix generator (`docs/value-definitions-design.md`) reads
the record and publishes `Sha256::layout`, the table of fields with its
`Fits` by the rule's theorem, `Sha256::stored: Stored<Sha256>`, and per
field an offset and a pair of accessors over the bytes with their laws
instantiated. Prove the generator, not the copies: the laws are §5's
theorems applied, never re-proved per record. At this stage SHA-256's
modules stay methods on the span, and their bodies say
`Sha256::block.put(ctx, cn, t, word)` where they say
`ctx.sha256_put_word(cn, (t << 2) + 64, word)`: no offset in a body, which
is `sha256-context-type`'s "done when" but for the receiver's type. The
accessors are `runtime fn`s over a span as today's are, so the programs
are the ones already linked and tested.

**Stage B: a `runtime fn` holds the record.** `ctx: Sha256` is the record
in the source and the span in the code. This is `datarepr` with a carrier
that is a span and not a word: `abs` is `Sha256::stored.read`, the
invariant is the length, a field read is `Stored::get` and a field
assignment (§20's `ctx.count := e`) is `Stored::put`, each a refinement
the generator cites from §5. What the generator must learn: a
representation held in a lent span (today a repr is one word,
`runtime-repr-types`); the length as part of the value, so `cn` leaves
every signature; a method's export under a symbol; and loads and stores
wider than a byte as a later optimisation that the alignment of layer 1
licenses (`rt-fixed-arrays-and-tables`, `x86-narrow-and-rotate-forms`).
The bound is the open part: reads are under the length word today, and a
record whose size is known wants that as one premise of the function
(`length = size`, which a Rust wrapper over `&mut [u8; 328]` gives for
free) and not a comparison per access. That is a fact in the sense of
`docs/compilation-vision.md` §2.3, and this stage is designed in its own
section once A is built and shows what the refinements look like.

## 7. Choices that are Minus's

1. **The name `Layout`.** The program compiler has a record of that name
   (`native_compile.hthr`: where a program's static words and buffers
   are). Nothing imports both today. Recommended: the library takes
   `Layout`, as Rust's does, and the program compiler's record is renamed
   (`Statics`) in a mechanical commit when a module first needs both.
2. **Byte order: in the codec or in the type.** Recommended: in the
   codec, written per field (`be`, `le`), so a `u32` is one type. The
   other reading is wrapper types (`u32be`), as Rust's `zerocopy` has.
3. **The declaration's spelling**: `laid record`, an attribute, or a
   `datarepr` clause. Recommended: a prefix generator named for what it
   does (`laid record`), since that is the mechanism declaration
   generators already use, with the default rule `repr(C)` order and
   `packed` as its argument.
4. **Field order is the written order** (Rust reorders by default, C does
   not). Recommended: written order, always; a reordering rule is a
   function over the table that a user may call.
5. **Stage A before stage B**, or B at once. Recommended: A first: it is
   a library and a generator in Heather, it removes every offset from the
   SHA-256 source, and B's design can then cite real lemmas.
6. **The alignment as an exponent** (§3, as built). The other reading is
   the alignment itself with a `Layout::Valid` premise on the theorems
   that need a power of two, which reads `Layout(4, 4)` for a `u32` and
   pays a premise at every use. Recommended: the exponent, with named
   layouts (`Layout::word(2)`, and constants for the word types once
   layer 3 names them) so a client seldom writes one.

## 8. Order of work

1. Layer 1 with its theorems (built), and the run-time twins of §4 with
   theirs (after `issues/bitvec-shift-mask-arithmetic.md`, whose laws
   their agreement theorems are).
2. Layer 2 (built): `Fits`, the in-order rule, the check by evaluation.
   Layer 3: `Stored` for words, arrays and records, and its laws.
3. Stage A's generator; SHA-256's modules over generated accessors, the
   linked assembly unchanged or its change explained.
4. Stage B's design section, then its rounds.
