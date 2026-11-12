# Layout as a library, and records laid over bytes

Status: **2026-11-12: layers 1, 2 and 3 are built on PR #551, and so are
the first pieces of layer 4: big-endian words read and stored by compiled
code, proved to be the codec's, which SHA-256's modules now use; fields
as values with their laws (`Part`, §5.3); the declaration
`laid record T { … }`, which reads each field's codec off its type and
publishes the record's codec and one part per field (§6.2, stage A); and
SHA-256's context as a record over its span, declared that way.
Accessors that name a field in a `runtime fn` body, and the record held
by a `runtime fn` (stage B), are design.**
Minus's direction (2026-11-12, the native thread): SHA-256's context goes
"straight to laid out fields, we're going to want them very soon
regardless", and "laying out should be something that's easy to use
relatively separately as well, similar to how Rust's layout api works …
so you can do it dynamically too for runtime layouting, etc. But ideally
better with proofs". What goes past those words was marked **proposed**
and put to Minus as six choices; §7 has them as decided the same day.

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

**Built** (`lib/std/machine/stored.hthr`): the record, `get` and `put`,
three laws, the codecs, and what a field of a stored record reads as
(the projection laws, below).

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

- `Stored` values: `Stored::byte`; `u16_be`, `u16_le` and so on to
  `u64` (from `bitvec_bytes`, a vector's entries as a list, which moved
  to `vector.hthr` from the arena); `s.array(n)` for `[A; n]`, elements a
  stride apart; `s.then(t)` for a pair, the second at `extend`'s offset;
  `s.padded()`; and `s.map(to, from, back)`, which is how a record is
  stored as its fields in order. Byte order is part of the codec and not
  of the type, as `rt-fixed-arrays-and-tables` asks: SHA-2 is big-endian,
  ChaCha20 little-endian, and both hold a `u32`. Padding is written as
  zeros and not read.
- **The projection laws**, for reads: a field read out of a stored
  record is the field's own codec at the field's offset, and element `i`
  of a stored array is the element's codec `i` strides on.
  `get_then_fst` and `get_then_snd` (the second at
  `s.layout.offset_of(t.layout) + at`), `get_padded`, `get_map` (which is
  `refl`), and `get_array_nth`, stated through the array's entries as a
  list (`vector_entries(…).nth(i) = Some(s.get(bytes, i * stride + at))`)
  because `[A; n]` has no index of its own and the specifications these
  meet hold lists (`Sha2::schedule`). They rest on one list law, a window
  of a window (`List::window_window`). The probes prove SHA-256's count
  to be `Stored::u64_be().get(bytes, 320 + at)` and schedule word `i` to
  be `Stored::u32_be().get(bytes, i * 4 + (64 + at))` by these laws alone,
  which is the statement a generated accessor is proved against (§6).
  The same for stores is §5.3, where a field is a value that carries
  both.
- **A word is its bytes at their indices**: `get_be_bytes`, `get_le_bytes`
  (the word of `bytes.vector_at(at, k, 0)`, the `k` entries from `at`) and
  `put_be_bytes`, `put_le_bytes` (`bytes.update_from(at, …)`, the entries
  stored one at a time). This is the form compiled code meets: it reads
  and stores a byte at a time (§6.1).
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

### 5.3 Parts: a field as a value (built)

`lib/std/machine/part.hthr`. Rust's `offset_of!` gives a number; what a
proof wants of a field is the number and what it means. A
`Part<A, B>(whole)` is a `B` inside a stored `A`:

```heather
record Part<A, B>(whole: Stored<A>) {
    offset: Nat,
    codec: Stored<B>,
    of: A → B,                  // the part of a whole
    with: A → B → A,            // the whole with the part replaced
    within: codec.layout.size + offset <= whole.layout.size,
    reads: …,                   // codec.get(bytes, offset + at) = of(whole.get(bytes, at))
    frames: …,                  // bytes changed only inside the part read as `with`
}
```

`reads` is the projection law of §5.2 as a field. `frames` is the law for
stores in its general form: where two lists agree on the whole's bytes
before the part and after it, the whole read from the changed one is the
whole read from the other `with` what the part's codec reads in the
changed one. A store through the codec is its first instance
(`Part::get_put`: `whole.get(p.codec.put(bytes, p.offset + at, b), at)
= p.with(whole.get(bytes, at), b)`), and a store by compiled code is the
second (§6.1). Stated over the changed bytes and not over `put`, it also
covers a part written a byte at a time, or by another function that is
proved to touch nothing else.

Parts are made by combinators, each proved once: `Part::all`, `fst` and
`snd` of a `then`, `padded`, `mapped`, `element(s, n, i, inside)` of an
array (whose `of` is `vector_index` and whose `with` is `vector_update`,
both new in `vector.hthr` with their laws and `vector_ext`), `then` for a
part of a part (offsets add), and `field` for a part of a record's fields
as a part of the record (`Stored::record` is the fields padded and read
through the constructor). So a record's parts are compositions, its
offsets are computed and are numerals by evaluation, `of` and `with`
reduce to the record's own projection and `with { f = … }` by `refl`, and
both laws come with no proof written for the record. The probes
(`lib/_tests/std/machine/part_tests.hthr`) do this for a header with
padding inside it and after it (a byte, a `u64` at 8, three `u16`s at 16,
24 bytes), for an element of an array of pairs at open codecs, and refuse
a law stated at the packed offset, a fourth flag, and a hand-made part
whose projection is not the one at its offset.

What it costs: a part is a dependent record with two proofs, so a
composition of five is a term of that depth. Offsets and `of`/`with`
still reduce by `refl` at SHA-256's record (§6.2); a record of hundreds
of fields would want the generator to publish each offset as a `def`
with its equation and not recompute it, which is the usual closed-verdict
trade.

## 6. Layer 4: a record laid over a span

### 6.1 Built: words as compiled code

`lib/native/runtime/stored_words.hthr` has the run-time half of a word
codec: `List::u32_be_within(length, i)` and `List::u64_be_within`, which
read a big-endian word from a span under its length word, and
`put_u32_be_within`, `put_u64_be_within`, which store one. Each is a
`runtime fn` (they were SHA-256's `sha256_word_at` and `sha256_put_word`,
moved and renamed) with a theorem that it is the codec's:

```heather
theorem List::u32_be_within_stored(self span: List<u8>, length, i: u64, inside: i.toNat() + 4 <= length.toNat()):
    span.u32_be_within(length, i) = Stored::u32_be().get(span, i.toNat()).zero_extend(32)

theorem List::put_u32_be_within_stored(self span: List<u8>, length, i, word: u64,
    inside: i.toNat() + 4 <= length.toNat(), own: length.toNat() <= span.len()):
    List::put_u32_be_within(span, length, i, word) = Mutated(Stored::u32_be().put(span, i.toNat(), word.truncate(32, 32)), word)
```

A word in compiled code is 64 bits, so the read is the `u32` widened and
the store takes a word's low half. The bounds are the caller's: the word
is inside the length word, and for a store the length word is inside the
span. The proofs are two steps that any width and either byte order
repeat: bytes joined by shifts and `|` are the codec's word
(`BitVec::be_join_32`, over `BitVec::bor_concat`), and the span's entries
at `at`, `at + 1`, … are the window's (`get_be_bytes`, `put_be_bytes`).
With §5.2's laws a body that stores a word and reads another is reasoned
about as `Stored::get` and `Stored::put` (the probes `put_then_get`,
`put_leaves_the_other` in `lib/_tests/native/runtime/stored_words_tests.hthr`).

The same four are stated at a part (`u32_be_within_part`,
`put_u32_be_within_part` and the two for eight bytes): a word compiled
code reads where a part lies is `p.of` of the whole the span holds,
and a word it stores there leaves `p.with` of it. The premises are the
part's codec being the word's (`refl` for a field of that type), the
index being the part's offset, and the two bounds.

So what the generator of stage A has left to publish per field is small:
the part (a composition), and the accessors' laws as instances of those
four.

### 6.2 The declaration

What the source should read as (the first sketch, kept for the stages it
names; the declaration as built is below, and a byte order per field as
written here would need the generator to be handed the record's syntax):

```heather
laid record Sha256 {
    hash: [u32; 8] be,
    working: [u32; 8] be,
    schedule: [u32; 64] be,
    count: u64 be,
}

runtime fn Sha256::push(mut self ctx: Sha256, byte: u8) → u64 { … ctx.count := ctx.count + 1; … }
```

In two stages, because the first needs nothing new in the runtime
generator and the second is the generator's own round.

**Stage A: the declaration generates over the library.** A generator
reads the record and publishes `Sha256::layout`, the table of fields with its
`Fits` by the rule's theorem, `Sha256::stored: Stored<Sha256>`, and per
field an offset and a pair of accessors over the bytes with their laws
instantiated. Prove the generator, not the copies: the laws are §5's
theorems applied, never re-proved per record. At this stage SHA-256's
modules stay methods on the span, and their bodies say
`Sha256::schedule.put(ctx, cn, t, word)` where they say
`ctx.put_u32_be_within(cn, (t << 2) + 64, word)`: no offset in a body, which
is `sha256-context-type`'s "done when" but for the receiver's type. The
accessors are `runtime fn`s over a span as today's are, so the programs
are the ones already linked and tested.

Stage A needs no change to the compiler if it is spelled as a generator
run after an ordinary record, which is how `congruences` is run today
(`lib/std/tactic/derive.hthr`):

```heather
record Sha256 { hash: [u32; 8], working: [u32; 8], schedule: [u32; 64], count: u64 }
generate laid(Sha256, …);        // the byte order, and anything a field's type does not say
```

A prefix generator runs over a `fn`, a `theorem` or a `def` and not over a
`record` (`docs/value-definitions-design.md` §3.1), so `laid record` as
written above is that mechanism extended, a change to the language, and
§7 item 3 is where it is chosen. The codec the generator builds is the
library's own composition, which checks today for this record (the probe
`sha256_stored_layout`): the fields' codecs joined by `Stored::then`,
padded, and read through the record's constructor by `Stored::map`, whose
round trip is `refl` because a record is its fields.

**Built: the declaration** (`lib/std/machine/laid.hthr`). It is the
record's own, under a prefix (§7 item 3, decided: prefix generators
extended to records, `docs/value-definitions-design.md` §3.5):

```heather
laid record Meters { value: u32 }
laid(endian := BigEndian, order := AsWritten) record Header { tag: u8, length: u64, flags: [u16; 3] }
```

It publishes `Header::stored(): Stored<Header>` and, for each field,
`Header::length_part(): Part<Header, u64>(…)`, and nothing else. The
layout is `Header::stored().layout` (`Layout(24, 3)` by `refl`), an
offset is `Header::length_part().offset` (8), and the laws for a read and
a store at a field are the part's own, so the generator proves nothing
and neither does its caller.

**Each field's codec is read off its type.** A `u8` is a byte; a word of
16, 32 or 64 bits is stored in the byte order the declaration names
(`endian`, the machine's little-endian where none is named), which is
§7 item 2 as decided: the order is the codec's and a `u32` is one type;
`[A; n]` is `n` of `A`'s codec; and any other type `R` is stored by
`R::stored()`, which is what `laid record R` publishes, so records nest
and their parts compose (`Leg::header_part().then(Header::length_part())`
is at the sum of the offsets, and its `with` is the nested record update,
by `refl`). A record whose bytes its types do not say names its codecs,
one per field: `laid(codecs := [Stored::u32_be(), Stored::u32_le()])`.
The arguments are named because a parameter with a default has no
positional slot.

**Where the fields lie is the declaration's choice** (§7 item 4, decided
against the recommendation here). `order := AnyOrder`, the default, lets
the declaration place the fields, and nothing may read an offset off the
source: it is `T::f_part().offset`. `order := AsWritten` is C's rule,
each field after the one written before it, for bytes that are a format
someone else reads. Today both give the written order; the rule that
chooses is `issues/laid-field-order-chosen.md`. SHA-256's context says
`AsWritten`, because its functions' bodies still write the offsets out.

The probes (`lib/_tests/std/machine/laid_tests.hthr`) hold all of that:
the bytes of a closed header, a record of one field in the machine's
order, a record of records, arrays of arrays, codecs named by hand, the
same call written as `generate laid("Late", endian := BigEndian);` after
a record declared before, and refusals, each with its reason: a codec
count that is not the field count, a codec that does not store its
field's type (after which the record's name is free, the declaration
being one transaction), a type that is not a record, a field whose type
has no codec to read off (`Nat`, a word of 24 bits), a record laid out
twice, and a prefix that is no generator.

Two things the generator met, both filed. A member of a group
cannot cite an earlier member (`generate-group-internal-references`), so
a part's type spells the record's codec out and not `Header::stored()`;
the two convert, and a function declared at
`Part<Header, u16>(Header::stored())` accepts a composition of generated
parts, but a diagnostic prints the long form and the group's text grows
with the square of the field count. And a nullary constructor inside a
pattern was read as a variable where the scrutinee comes from
`let x <- t;` (`deep-pattern-ctor-unknown-column-type`, found writing
this generator, where a type of two constructors was taken for a record,
and fixed in the same round); the generator's matches are still written
a level at a time.

Not built of stage A: accessors as `runtime fn`s that name the field
(`ctx.schedule_put(cn, t, word)`), which would take the offsets out of
SHA-256's bodies. A generated accessor is a call, and with no inliner it
costs one in the compression loop, so that waits for stage B or for
inlining and is not done by default.

**SHA-256's context, declared:** `lib/native/crypto/sha256_context.hthr`.
`laid(endian := BigEndian, order := AsWritten) record Sha256 { hash, working, schedule, count }`,
one part per word of each array as a composition, and `Sha256::of(ctx)`,
the context a span holds. The offsets the SHA
modules write in their bodies are theorems by `refl`
(`Sha256::schedule_at(i)`: `i * 4 + 64`; `count_at`: 320; the layout is
`Layout(328, 3)`), and each access is tied to the record:

```heather
theorem Sha256::schedule_put(ctx: List<u8>, cn, at, word: u64, i: Nat, here: i < 64, place: at.toNat() = i * 4 + 64, …):
    Sha256::of(List::put_u32_be_within(ctx, cn, at, word).after)
        = (Sha256::of(ctx) with { schedule = vector_update(Sha256::of(ctx).schedule, i, word.truncate(32, 32)) })

theorem Sha256::count_is(ctx: List<u8>, cn: u64, inside: 328 <= cn.toNat()): sha256_count(ctx, cn) = Sha256::of(ctx).count
```

Each is one application of a `stored_words` theorem, with `refl` for the
codec and the offset. Nothing in SHA-256's bodies or its assembly
changes: this is the statement side, which is what stage B's refinements
will cite. What a correctness proof of `sha256_compress` against the
specification would do with it is rewrite each store and read of the
loop into an update or a field of a `Sha256`, and never mention a byte.

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

## 7. The choices, as Minus decided them (2026-11-12)

1. **The name `Layout`**: the library takes it, as Rust's does. The
   program compiler's record of that name (`native_compile.hthr`) is
   renamed (`Statics`) in a mechanical commit when a module first needs
   both.
2. **Byte order is the codec's**, not the type's: a `u32` is one type.
   The declaration names the order of the words it reads codecs off
   (`endian`), and a record with both orders names its codecs.
3. **The declaration's spelling is `laid record T { … }`**: prefix
   generators extended to records. "`generate` is fine now, but not
   amazing", so the `generate` form stays as the call the prefix makes
   and is not what a record is declared with.
4. **Field order is not the written order.** The recommendation here was
   written order always; Minus: reordering should be "magical" by
   whatever setup `laid` uses, and the ability to decide is valuable,
   though nothing complex is needed yet. So the default lets the
   declaration place the fields and a declaration that needs C's rule
   asks for it (`order := AsWritten`); the rule that chooses is
   `issues/laid-field-order-chosen.md`.
5. **Stage A before stage B**: agreed, and A is built.
6. **The alignment is held as an exponent**: agreed.

Open, raised in the same message: "the amount of functions as fields",
with no obvious best way seen. Read here as two things. The declaration
publishes one function per field (`T::f_part()`), and `Stored` and `Part`
are themselves records of functions (`read`, `write`, `of`, `with`). What
could stand beside them is a layout as first-order data: an inductive
description (a byte, a word of a width and an order, an array, a pair,
padding) with the type it stores computed from it, one interpreter giving
its `Stored`, and a field named by a path whose `Part` is computed. A
record would then publish one value, and the declaration, a rule that
reorders, and run-time code would all read the same description instead
of terms. Filed with what it would cost
(`issues/layout-first-order-description.md`), not built.

## 8. Order of work

1. Layer 1 with its theorems (built), and the run-time twins of §4 with
   theirs (the laws their agreement theorems are landed with
   `issues/bitvec-shift-mask-arithmetic.md`; the twins are not built).
2. Layer 2 (built): `Fits`, the in-order rule, the check by evaluation.
   Layer 3 (built): `Stored` for words, arrays and records, its laws, and
   fields as values with the laws for reads and for stores (`Part`,
   §5.3).
3. Words as compiled code (§6.1, built for big-endian `u32` and `u64`;
   SHA-256's modules read and store through them: `sha256_compress.s`
   is byte for byte what it was, and the three stream files change
   because the count's accessors now call the eight-byte ones, one call
   deeper). Stage A's generator (`laid.hthr`, built, declared as
   `laid record`) and SHA-256's context declared with it
   (`sha256_context.hthr`, built). Left of
   stage A: accessors that name a field in a `runtime fn` body. Two probes say what the generator may publish:
   a plain `fn` becomes run-time code afterwards by
   `generate runtime("Name");`, and a `def` numeral is read in a
   `runtime fn` body, so an offset can be a published constant.
4. Stage B's design section, then its rounds.
