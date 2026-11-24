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
64 bits), `docs/native/datarepr-design.md` §5.2 ("layout is DATA": a programmatic
layouting value users can replace), `docs/compilation-vision.md` §2.4 and
§2.5 (representations; memory a function is lent).

## 1. What there is to build on

- **A span is a list of bytes and a length word**, lent to a `runtime fn`
  (`docs/native/native-one-compiler-design.md` §2.6). Reads are under the length
  (`byte_within`), stores too (`put_within`). No meaning mentions an
  address.
- **A window of a list is a lens** (`lib/std/data/list_window.hthr`):
  `window`, `put_window`, and the laws either way round, with what a store
  leaves before, inside and after it.
- **A word is its bytes in either order**
  (`lib/std/bitvec/bitvec_bytes.hthr`): `bytes_le`, `of_bytes_le`,
  `bytes_be`, `of_bytes_be` with both round trips, over `[BitVec(8); k]`.
- **A field path is a place** (`docs/language/sequencing-surface-design.md` §20):
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
  `docs/native/datarepr-design.md` §5.2's "an arcane hand layout proves the same
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
`record` (`docs/metaprogramming/value-definitions-design.md` §3.1), so `laid record` as
written above is that mechanism extended, a change to the language, and
§7 item 3 is where it is chosen. The codec the generator builds is the
library's own composition, which checks today for this record (the probe
`sha256_stored_layout`): the fields' codecs joined by `Stored::then`,
padded, and read through the record's constructor by `Stored::map`, whose
round trip is `refl` because a record is its fields.

**Built: the declaration** (`lib/std/machine/laid.hthr`). It is the
record's own, under a prefix (§7 item 3, decided: prefix generators
extended to records, `docs/metaprogramming/value-definitions-design.md` §3.5):

```heather
laid record Meters { value: u32 }
laid(endian := BigEndian, order := AsWritten) record Header { tag: u8, length: u64, flags: [u16; 3] }
```

It publishes `Header::stored(): Stored<Header>` and, for each field,
`Header::length_part(): Part<Header, u64>(…)` and
`Header::length_at: u64`, and nothing else. The layout is
`Header::stored().layout` (`Layout(24, 3)` by `refl`), an offset is
`Header::length_part().offset` (8), and the laws for a read and a store
at a field are the part's own, so the generator proves nothing and
neither does its caller.

**`T::f_at` is the offset as a word**, for compiled code: a `runtime fn`
body writes `ctx.u64_be_within(cn, Header::length_at)` and
`(i << 1) + Header::flags_at`, and the reflector reads the name as the
literal it is. The generator does not copy the layout rule to get the
number. It asks the host what the part's own `offset` computes to
(`Numeral`, `docs/metaprogramming/host-elaboration-interface-design.md` §28, new with
this) and publishes that literal, so whatever codec a field has, derived
or named by the caller, the word is the library's answer; that it is
(`Header::length_at.toNat() = Header::length_part().offset`) is `refl`.
A word and not a `Nat` because that is what a body adds to; sixty-four
bits because a `runtime fn`'s words are.

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
chooses is `issues/laid-field-order-chosen.md`. SHA-256's context leaves
the order to the declaration: its functions' bodies name `Sha256::…_at`
and write no field's offset as a number (§9.5, round 1).

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
(`ctx.schedule_put(cn, t, word)`). A generated accessor is a call, and
with no inliner it costs one in the compression loop, so that waits for
stage B or for inlining and is not done by default. The offsets are out
of SHA-256's bodies without them, by the published words.

**SHA-256's context, declared:** `lib/native/crypto/sha256_context.hthr`.
`laid(endian := BigEndian) record Sha256 { hash, working, schedule, count }`,
one part per word of each array as a composition, and `Sha256::of(ctx)`,
the context a span holds. `sha256_block` and `sha256_stream` import it
and reach every field by its published word:

```heather
runtime fn List::sha256_take_block(mut self ctx: List<u8>, cn: u64, block: List<u8>, bn, i: u64) → u64 decreases (64 - i).toNat() {
    if h: i < 64 {
        ctx.put_within(cn, i + Sha256::schedule_at, block.byte_within(bn, i));
        …
```

(The compression's own loops were written this way until they became
functions of the record, §9.5 item 4.)

What a body still writes is a word's place within its array
(`Sha256::working_at + 16` is the fifth working variable), which is the
array's own layout and not the record's. Each access is tied to the
record by a theorem stated at the names:

```heather
theorem Sha256::schedule_put(ctx: List<u8>, cn, at, word: u64, i: Nat, here: i < 64, place: at.toNat() = i * 4 + Sha256::schedule_at.toNat(), …):
    Sha256::of(List::put_u32_be_within(ctx, cn, at, word).after)
        = (Sha256::of(ctx) with { schedule = vector_update(Sha256::of(ctx).schedule, i, word.truncate(32, 32)) })
theorem Sha256::count_is(ctx: List<u8>, cn: u64, inside: SHA256_CONTEXT_BYTES <= cn.toNat()): sha256_count(ctx, cn) = Sha256::of(ctx).count
```

Each is one application of a `stored_words` theorem, with `refl` for the
codec and the offset, and the count's bound comes from the part's own
`within`, so no proof here would change if the fields moved. What Rust
must agree on is two numerals of the module, `SHA256_CONTEXT_BYTES` (the
bytes Rust lends) and `SHA256_DIGEST_AT` (where the hash value is), each
held to the declaration by a `refl` theorem and copied to Rust by
`scripts/linked` (`generated/CONSTANTS.tsv`). The probes pin today's
numbers (0, 32, 64, 320; `Layout(328, 3)`) as tests, not as library.

The cost of naming, until the IR folds constants
(`issues/function-ir-pass-arithmetic-folds.md`): `Sha256::working_at + 16`
is an addition of two constants at run time, and `i + Sha256::hash_at`
adds zero. What a correctness proof of `sha256_compress` against the
specification would do with these theorems is rewrite each store and
read of the loop into an update or a field of a `Sha256`, and never
mention a byte.

**Stage B: a `runtime fn` holds the record.** `ctx: Sha256` is the record
in the source and the span in the code. Its design is §9.

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

## 9. Stage B: a `runtime fn` that holds the record (design, 2026-11-12)

What the statement is, what is proved once, where the hard part is, and
the rounds. Round 1 and the theory of round 3 are built (§9.5 says which
part of each); the rest is design.

### 9.1 What the source reads as, and what is claimed

```heather
runtime fn Sha256::count_byte(mut self ctx: Sha256) → u64 {
    ctx.count := ctx.count + 1;
    ctx.count
}
```

The receiver is the record. A field read is the record's projection and a
field assignment is §20's `x.f := e` (`docs/language/sequencing-surface-design.md`),
so the function is an ordinary Heather function of `Sha256`, and every
theorem about SHA-256 is about that function and never about bytes. No
length word is written: the record has a size.

The code is lent a span, as today. What is published for `f` is, in
words: at every file whose first span `own` is at least the record's size
long, the program's run returns `f(Sha256::of(own), args).value` and
leaves a span `own'` of the same length, with
`Sha256::of(own') = f(Sha256::of(own), args).after` and every byte past
the record as it was. `Sha256::of` is `T::stored().get(_, 0)`, so this is
a statement in the library's terms, and a caller in Rust reads it as
"the 328 bytes I lent hold the context the Heather function returns".

### 9.2 What is proved once: a second meaning, and that the two agree

The runtime language has one meaning of a computation over a span: bytes
to bytes (`FTm::sem`, `rt_file.hthr`). A function over a record cannot be
pinned to that meaning by conversion, which is how every `runtime fn` is
pinned today, because `r.count` and "eight bytes at 320 joined" are equal
by a theorem (`Part::reads`) and not by computation. So the same terms
get a second meaning. **Built**, for bodies without a loop:
`lib/native/runtime/rt_held.hthr` and `rt_held_fields.hthr`, probes in
`lib/_tests/native/runtime/rt_held_tests.hthr`.

- **One term language.** `FTm` gains no node. A field read is a bound
  call of a pure function of the program and a field store is a call of
  one of its computations, as a span's word is read and stored today. A
  held world (`HWorld<A>`) is the program's world with a mark on some of
  those functions: `Reads(width, get)` on a pure one, `Writes(width,
  set)` on a computation, with `get: A → BitVec(width)` and
  `set: A → BitVec(width) → A`. A reader takes the span's place and its
  length word; a writer takes those and the value.
- **Two meanings.** `FTm::held` answers `Mutated<A, R>`, the record the
  computation leaves and its value, which is what a function of the
  record answers. A bound call of a reader is `get(a)`, a writer's call
  leaves `set(a, value)`, and every other term is the byte meaning's. The
  span's bytes are an operand it carries for those other terms and never
  part of its answer. (An answer holding the bytes too was the first
  attempt: every branch then sits under a projection, and a projection
  of a stuck `match` is not the match of the projections, so a function
  with a branch could not be pinned.)
- **The pin is by conversion**, as every pin is. With the marks
  `λ t => t.count` and `λ t v => t with { count = v }`, a function of
  the record is its reflection's held meaning by `refl`, through a
  branch too.
- **The span holds the record** is `whole.Holds(own, n, a)`: the record
  is inside the length word `n`, the length word is inside the span, and
  `a` is what is read at the span's start. The length word is in it
  because compiled reads and stores are under one (§9.3, point 1).
- **The agreement**, `FTm::held_runs`, by induction over the term, once:
  where the span holds a record and the world is `Sound`, the held
  meaning's value is the byte meaning's, and the bytes the byte meaning
  leaves hold the record the held meaning leaves, under the same length
  word. `Sound` is a tuple, one proof per marked function.
- **Each of those proofs is one application** (`rt_held_fields.hthr`):
  `Stored::held_read` and `Stored::held_write` are proved once for every
  record, field and codec with an accessor (§9.4), from the part's laws
  and the accessor's. A generator writes the tuple and proves nothing.
- **What a held body may be** is a verdict, `FTm::kept`, `True` by
  evaluation at a closed term: every call a marked one on the span's own
  length word, no byte stored but by a writer, no loop, nothing lent. The
  last three are the rounds still to come, and a body outside it is
  refused and not silently given the byte reading.
- **A function's statement** is `FFun::held_runs` read at the function:
  `Agrees<A, R>(whole, length, F(a, xs…), f(own, length, xs…))` where
  `whole.Holds(own, length, a)`, with `F` the function of the record and
  `f` the compiled function of bytes. It is three things by conversion
  (the pin of the held meaning to `F`, the reflection's of the byte
  meaning to `f`, the verdict) and that one theorem. The probes prove it
  so for two compiled functions, one with a branch and an operand, and
  `f::runs_over` then says the program's run is `f`.

The function that is compiled, linked and exported is the reflection
itself, an ordinary function of bytes for which everything downstream is
unchanged (`CompileSpan`, links, lends, `compile-x86`, `scripts/linked`).
Prove the generator, not the copies: nothing is proved for `f`.

What this design costs against the one first written here (two new
nodes and an expansion to the words' code): a field access is a call in
the compiled code, where the expansion would have inlined it. Inlining a
small callee is the lowering's to do for every function and not this
theory's, and without it there is no expansion to prove anything about.

What it does not say yet: that the span is as long after as before, and
that the bytes past the record are as they were (`Holds` after says the
length word is still inside the span, which is what the next field
access needs); neither is needed by a loop (§9.3) and both wait for a
client. And a field narrower
than a word is in the theory (the marks carry a width, and the accessor's
`kept` law is what `held_read` and `held_write` use) but not yet in
compiled code: a function that writes a span takes and returns 64-bit
words for now (`issues/runtime-repr-narrow-words.md`).

Two things the kernel's conversion asked of the statement, both in the
module's comments: a reader's promise is stated of `FTm::read`, the call
with its operands under the program's own type table, because
`FTm::value` reads them under the table of the world at the file and
where the two spellings meet at a concrete world the kernel evaluates
the callee at both worlds to tell them apart
(`issues/conversion-respelled-world-compares-reflection.md`); and a
function's theorem keeps the body's held meaning bare, read at the
declared result along an equation and not through a cast, so that a pin
through a branch stays a `match` against a `match`.

### 9.3 The hard part: a span too short to hold the record

The byte meaning is total: a store past a list's end does nothing and a
read there is zero, and the class states a function's run at **every**
span (`CompileSpan.runs`, `FFun::Guarded`). The agreement is true only
where the span holds the record. Three consequences, in the order they
bite:

1. **The length word.** Reads and stores are under a length word, and the
   record-level source has none. **Built**: a field's reader and writer
   are called on the span's own length word, the function's parameter
   (`FTm::kept` refuses any other), and the statement's premise is that
   the record is inside that word and the word inside the span
   (`Stored::Holds`). So compiled code stays inside what its caller says
   it lent, whatever that is, where the record's size as a literal in
   the length's place would read and store past a short span. The
   comparisons against a length the path already knows to be at least
   the record's size are the lowering's to drop, later.
2. **A function without a loop** has its byte meaning at every span, so
   it is an instance of the class as it is, and the agreement is a
   theorem beside it. Nothing new is needed.
3. **A loop** needs a function of bytes at every span, and for a
   record-level loop the function the source names is the record-level
   one, which says nothing where the span holds no record.

**Built: the passes the code counts.** The loop's compiled code already
counts its passes (`Fun::meas_passes`, `2^64 - 1`), and with the count
spent it runs the body once more with the self-call answered by the first
word it would have moved. So the code computes a function of bytes that
needs no equation at all: the body iterated that many times,
`FFun::rounds(n, pass, stop)`, where `pass` is the body as a function of
the passes after it and `stop` is what answers with the count spent. It
is total at every span, the class's statement is unchanged
(`CompileSpan`, with a second way to build an instance,
`FFun::compile_counted`, from `FFun::counted_sound`), and no function
that exists changes its statement. What the iteration computes at a span
too short to hold the record is nobody's theorem and nobody needs it.

Where the span holds a record, the iteration is the function of the
record (`FFun::counted_held`, `rt_held_loop.hthr`), by an argument a pass
at a time: a pass at the record and a pass at the bytes agree while the
span holds the record (`Pass`, `FTm::tail_held_runs`), each pass lowers
the measure, and the measure is below the count. What the proof takes
from the function is its own equation at records (`FFun::HeldGuarded`:
the body with any recursion that agrees with the function below the
measure is the function), which the generator reads off the function's
companions `ext` and `irrel`, and that the measure is a word's `toNat`.
That the recursion in the body is at a lower measure is not asked for
separately: it is read off the equation (`FFun::falls`), since an
equation that holds for every recursion agreeing below the measure
cannot read the recursion at or above it.

This replaces the floor this section recommended before it was built
(one number per function in `CompileSpan` and `FFun::Guarded`, the least
length they speak of): the floor changed the class and every caller's
obligations to say something about spans the theorem never uses. The
other routes weighed then, a proof as a parameter of a `runtime fn` and a
loop written over the span that calls held functions, are not needed for
this either. An exact codec (`put(b, at, get(b, at)) = b`) is not needed:
nothing is carried from the record back to bytes.

**Padding.** `Stored::put` writes zeros into padding. Loops do not ask
for more (above); a `put` that leaves padding as it finds it makes
every codec a lens in the full sense (`put(b, get(b)) = b`,
`put(put(b, x), y) = put(b, y)`) and is its own library round.

### 9.4 What reads a codec

The reflector has to know which code reads a field: a word of four bytes,
most significant first, at offset 64. A field is a `Part` whose codec is
a term, and the code for a codec is found by a class keyed by that term
(`Accessor(codec)`, `lib/native/runtime/stored_accessor.hthr`, §10.2):
the instance holds the `runtime fn` that reads the codec's value under a
length word, the one that stores it, the word a value is held as, and
the two theorems that the calls are the codec's `get` and `put`. A
marked function's obligation (§9.2) is then one of two theorems for every codec that has
an accessor, `Stored::read_at_part` and `Stored::write_at_part`, built.
A field whose codec has no instance is refused by name.

(First written here: this reader needs a layout as data, a closed
description the reflector interprets. The class is the open form of the
same thing, and what was learnt trying both is §10.)

Indexing an array field by a word (`ctx.schedule[t]`) is a field read at
a computed offset. Its record meaning is total only with a bound, so the
node carries a test (`t < 64`, one comparison where the bytes take four
today) and reads zero past it, as a slice index would refuse; a bound the
path already knows is the same fact the length is.

Words narrower than 64 bits stay as they are in compiled code: a `u32`
field is read widened and stored from a word's low half, which is what
the two leaf theorems say (`issues/runtime-repr-narrow-words.md`).

### 9.5 Rounds

1. **Offsets by name** (no theory). **Built** (§6.2): `laid record`
   also publishes each field's offset as a word a `runtime fn` body
   reads, SHA-256's bodies name them, and its context drops
   `order := AsWritten`. This is what makes §7 item 4 safe to turn on,
   and it is all of `sha256-context-type`'s "no layout offsets in their
   bodies" that does not need the receiver's type. What it needed that
   was not foreseen: a generator could not get a number out of the
   layout library (`Whnf` is out of budget on `Nat::round_up`), so the
   host has a `Numeral` request, which stage B's reflector will use for
   the same reason.
2. **How a layout is found** (§10; `layout-classes`,
   `layout-first-order-description`), as Minus decides: a codec's
   compiled accessor by a class, a declared type's layout by a class,
   and a layout as data. A prototype of each checks.
3. **A held function without loops.** **Built**: the theory (§9.2: the
   marks, the held meaning, the agreement, the two field lemmas, the
   function's theorem) and the generator. `runtime fn T::m(mut self t:
   T, …)` at a `laid record` publishes `T::m::bytes` (the function over
   the span the code is compiled from), its instance and program as a
   function over a span does, `T::m::held` and `T::m::sound` (the marks
   and what they owe, one field lemma per field), and
   `T::m::runs_held`: where the span holds a record, the bytes'
   function answers what `T::m` answers and leaves the span holding
   the record it leaves. Nothing is proved about `T::m`. Probes:
   `lib/_tests/native/runtime/runtime_held_tests.hthr`.

   What the build found that the design did not have:

   - **A field access is the codec's accessor called at the field's
     offset** (`List::u64_be_within`, `put_u32_be_within`, …), found
     by the accessor class of §10.2. Nothing is compiled per field, and
     the marks are per accessor with the fields each reaches.
   - **The function of bytes is the reflection written out**, not the
     reflection's meaning: each value bound once (`HWorld::once`), each
     store followed by what comes after at the span it leaves
     (`HWorld::after`). A meaning stated at one file and compared with
     the meaning at another is compared environment by environment.
     Reads are bound where they are read, so a read before a store used
     after it is not the problem it is for a function of bytes written
     by hand.
   - **What is by conversion is proved at every callee** and read at
     the program's own (`HWorld::at`): with its own accessors in place
     the kernel unfolds an accessor it reaches on one side first, and a
     64-bit read cost a quarter of a declaration's budget
     (`issues/conversion-callee-unfolded-before-the-meet.md`).
   - **A check's verdict is an equation in every compile entry point**:
     as a proof of `check.IsTrue()` it was compared at a type the kernel
     computed, the whole lowering, wherever a link named an instance
     twice (`issues/conversion-proof-compared-at-computed-type.md`).
     This changed the span and the reading compilers alike.
   - A function that changes nothing (`self t: T`, a word) is compiled
     the same way, and a branch around the whole result is two ends.

   - **An array of words is its elements, each a part.** A field
     `[u32; 8]` whose element codec has an accessor is read by
     `vector_index(t.f, i, trivial)` at a literal `i`, which stands for
     the accessor's read where element `i` lies
     (`T::f_part().then(Part::element(codec, n, i, _))`, the parts of
     §6.1 composed, its offset by `Numeral`). A field whose new value
     differs from the old in an entry stores that entry: `t.f := [a, b,
     …]` is a store for each element, `t.f := vector_update(t.f, i, w)`
     one. The theory did not change: an element is one more entry of
     its accessor's mark, with the same field lemma. The marks name
     only the elements a function reaches (the literal offsets its
     accessors are called at, read off the reflection), so an array of
     sixty-four words costs a function that stores one of them one
     entry.
   - **compile-x86 exports a record function as its function over the
     span.** The row names the method (`Sha256::init`), the symbol is
     derived from the path (`sha256_init`), and the certificate's
     statement is at `T::m::bytes`.

   First customer: `Sha256::init` (`lib/native/crypto/sha256_stream.hthr`)
   is a function of the context, `s.hash := […]; s.count := 0`, the
   linked `sha256_init` is its code, and `Sha256::init_holds` says the
   span is left holding the context with the initial hash value and no
   bytes taken, with nothing proved by hand.

   What it does not take yet is
   `issues/runtime-record-function-limits.md`: a branch before the end
   with a store in it, operands and results other than 64-bit words,
   fields with no accessor, and the index spelled `t.f[i]`.
4. **Calls and loops**: a call of another function of the record
   (**built**, below); a loop (**built**, below and §9.3); an element at
   an index that is a word (**built**, below); and a word array's bytes
   (`sha256_take_block` and `sha256_begin` store bytes where words lie,
   which is a second part over the same bytes). Then SHA-256's
   functions are methods of `Sha256` whole, its entry points are exported
   as methods (`linked-export-of-a-method`, merged), and
   `sha256-context-type` closes.

   **An element at an index that is a word** is built
   (`lib/_tests/native/runtime/runtime_held_index_tests.hthr`):
   `t.f.at(i)` reads it and `t.f := t.f.put(i, x)` stores it, at an
   array of words, with `i` the word itself. They are methods of the
   vector type (`Vec::at`, `Vec::put`).

   The element **takes a proof that the index is inside**, and the
   proof is found, not written (Minus, 2026-11-13: a value for past the
   end is a sign of too little automation). `Vec::at`, `Vec::put`
   and `Vec::put_byte_be` (`stored_words.hthr`) each have a last
   parameter `inside: i.toNat() < n := bv_omega`: left out, the search
   reads the tests around the call (`if h: i < 64`) and the call is
   refused where it finds none. So a loop is written with a counter its
   test bounds every index by (SHA-256's schedule counts `j` to 48 and
   writes `W[j + 16]`). This was first built total (`vector_get(…, 0)`,
   `vector_update`, the code answering 0 past the end); those forms are
   now refused in a function of a record, with the form to write.

   Two steps, of which the first is built. *The source requires the
   proof*: each function is defined as the total one beside it, so the
   function of the record and its pin are unchanged, and the code still
   makes the accessor's compare, which the proof says is never failed.
   *The code drops the compare*: the record theory then has to carry
   each site's bound to the accessor's unchecked law, which is the same
   facts-on-a-path a callee's proof parameter needs (a caller's meaning
   names its callee as a total function of record and words today), so
   an index whose bound is an invariant and not a test (`Sha256::put`'s
   fill below 64) is tested where it is used for now.

   What the first step needed of the language:

   - *A found proof is one term* (`measure::lift_found`,
     issues/found-proof-differs-across-recursion-companions.md). Under
     `decreases` a body's syntax is elaborated once for each generated
     declaration, and a search that reads its context found a different
     proof each time; the kernel was then left comparing two proofs at
     the same head where the companions need one call. Each such proof
     is now a theorem `f#found_N` over the binders its goal and the
     facts about them name, found once and passed by name at the call.
   - *An `if h:`'s test is a fact a search can read* where a branch
     does not name `h` (issues/if-evidence-hidden-from-tactics.md).
   - *An operator on such a call*
     (issues/operator-on-call-with-defaulted-argument.md): a defaulted
     parameter is no reason to wait for an expected type, and a probe
     that fails only for want of a goal slot asks for the restart.

   - *Library.* A codec's accessor has a checked element reader and
     writer beside its word's (`Accessor`'s `read_at`, `write_at`,
     `stored_accessor.hthr`): the span's place and length word, the word
     the array begins at, its count, the index, and for a store the
     word. For big-endian words they are `runtime fn`s of two lines over
     the word accessors (`List::u32_be_at_within`, `stored_words.hthr`),
     with two laws each: inside the count it is the codec's `get` or
     `put` a stride on for each index, past it 0 or nothing. Nothing is
     compiled per array or per field.
   - *Theory* (`rt_held.hthr`). Two more marks: a pure function may be
     an indexed reader (`Indexes`) and a computation an indexed writer
     (`Stores`), each with the arrays it reaches, an array by the offset
     it begins at and then its count, and what it stands for a function
     of the record and the index word. The held meaning of a call reads
     the element off the record at the word its index variable is. What
     a mark owes at an array (`HWorld::Indexes`, `HWorld::Stores`) is
     proved once, for every record, array field and codec with an
     accessor (`Stored::held_index`, `Stored::held_store`,
     `rt_held_fields.hthr`): element `i` of an array that is a part of
     the whole is a part of the whole (`Part::element_in`, `part.hthr`),
     and the accessor's laws are the codec's there. A store's offset and
     count are read off the literals that bound them, as a field's
     offset is; a read needs no such knowledge.
   - *Reflector.* `Vec::at` at a field of the record stands for the
     accessor's checked read at its index word; a field's new value that
     is the field under `Vec::put`s is one store for each, the
     innermost first. The index is any word the body computes, and the
     proof is not read.
   - *Generator.* An array is marked whole, by its part: one entry and
     one application of the array's lemma, whatever its count.

   A loop over an array compiles with its record theorem (the probes'
   `Sched::expand` is the shape of SHA-256's message schedule, each word
   from two before it), and runs on bytes. The index is not yet spelled
   `t.f[i]`, which is surface and Minus's to choose.

   **SHA-256's compression is methods of `Sha256`**
   (`lib/native/crypto/sha256_schedule.hthr`, `sha256_working.hthr`,
   `sha256_compression.hthr`): `expand`, `begin`,
   `shift`, `set`, `turn`, `t1`, `rounds`, `end`, and `Sha256::run`,
   which is the four loops in a row, each with its record theorem from
   the generator. No body has an offset or a width. **They are the
   linked compression**: a function over a bare span calls a record
   function's code (`Sha256::run::bytes(ctx, cn)`, a callee the span
   reflector takes when it is a record function's, `rt_record_of`), so
   `sha256_compress` takes the block's bytes in and runs `Sha256::run`,
   and the stream's functions reach the same code through the context's
   own (below). The span spellings of the schedule and
   the rounds are deleted. Against the reference and the standard's
   vectors the linked code is unchanged in what it computes
   (`crates/linked/tests/sha256.rs`, short spans included); its program
   is three functions longer and its stack, which is counted by
   functions, deeper by as many frames. What a span
   function proves of such a call is only its bytes: `runs_held` is not
   carried up, since a span function states nothing about a record.
   Two things the methods needed:

   - *A store at a numeral after a call.* `s.shift(0); s.working :=
     vector_update(vector_update(s.working, 0, a), 4, e)` was refused,
     because which entries changed was told by comparing with the
     record's local. A field under `vector_update`s is now read as its
     stores whether an index is a word (the checked store) or a numeral
     inside the count (the accessor's own store where that element lies).
   - *The pin with the callees parameters.* A function is pinned to its
     reads and stores by a conversion against the function of the
     record. At the callees themselves the kernel advances the newer
     head, which is the function's side, and a loop called at a numeral
     (`s.rounds(0)`) is unfolded there pass by pass before the other
     side arrives at its name; `Sha256::run` ran past the budget, and
     which orders of calls did depended on the loops. So the statement
     is taken with every mention of a callee a parameter (`revert_into`
     at a global, an addition to the host's `Revert`:
     `docs/metaprogramming/host-elaboration-interface-design.md` §26), proved by `refl`
     under the parameters, where nothing has a body, and applied to the
     callees (`runtime_held_straight`). It is the remedy of the callee's
     tables and of a loop's iteration once more
     (`issues/conversion-callee-unfolded-before-the-meet.md`).

   A caller's generation carries its callee's program, and its cost
   climbed with the depth of the chain, so the round is flat: the loop
   calls `Sha256::t1` and `Sha256::turn`, where the span functions have a
   `step` that calls `turn`. The methods are three modules so that each
   is inside the library gate's rail under the test profile's binary
   (`issues/runtime-record-function-limits.md`, the log's last entry).
   The pin is tried at the callees first and at parameters where that
   runs out.

   The export's certificate needed the same remedy once more. Its
   return theorem compared the ending's word (`FTm::end_of(rest, m).word`)
   with the function's value, and the kernel advanced the function:
   the exported compression now reaches loops called at numerals, which then ran
   pass by pass. `compile-x86` states the theorem through
   `Ending::returns_written` and `Ending::returns_marked`
   (`rt_file_returns.hthr`), where the result is a parameter and the
   comparison is of two names.

   **The stream is the context's too** (`sha256_filling.hthr`,
   `sha256_padding.hthr`, `sha256_stream.hthr`, `sha256_one_block.hthr`): `Sha256::put` (a byte of
   the block), `push`, `zero`, `pad`, `close`, and over them `absorb`,
   `take`, `update`, `finish`, `take_block` and `compress`. No function
   of the linked SHA-256 is written over a bare span, and none names an
   offset, a width or `Mutated`. A byte of the block is a quarter of a schedule
   word, and `put` is one store of it:
   `s.schedule := vector_with_byte_be(s.schedule, at.toNat(), byte.truncate(8, 56))`,
   the array with byte `at mod 4` of word `at div 4` replaced, most
   significant first. Its code is the checked byte accessor over the
   array's bytes (`List::put_byte_at_within`, `stored_words.hthr`: one
   byte at `base + at` under `at < 4 * count`, nothing past it), on the
   store mark the word store already had, so the layout holds no second
   part over the same bytes. What makes it sound is one lemma about the
   codec, that a word stored with one byte replaced is that byte stored
   (`Stored::u32_be_put_with_byte`), and one for every array
   (`Stored::held_put_byte`, `HWorld::stores_bytes_array`). Taken for
   big-endian words of four bytes at an index that is a word; a byte
   read is not built.

   **A span that is only read** is what the last six needed, the message
   and the block:
   `Sha256::absorb(mut self s: Sha256, message: List<u8>, mn, j, fill: u64)`.
   After its record a function takes each span it only reads, the bytes
   and then the length word, and then its words; the code takes the
   record's span first, and each read span's place and length word where
   the function takes the span. `FTm::held` was already a meaning at any
   rest of a file, so the theory is unchanged. What changed is the
   generator: the marks, what they owe, and a loop's function, measure
   and equation are each a function of the rest of the file, and the
   theorem reads them at the function's own spans,
   `T::m::runs_held(own, t, length, src, sn, …, holds)`. A span goes to a
   callee or to the loop's next pass as it came, in its own place, so
   the callee's function of the record is read at the same file. One
   thing is particular to a loop: its recursion takes the span's bytes
   like any parameter, and `T::m::ext` asks that two recursions agree at
   every span, where the code's answer is known only at the file's. The
   body never varies the span, so each recursion compared is read at the
   file's span whatever it is handed, and the equation still converts
   (`runtime_held_counted`). Probes
   `lib/_tests/native/runtime/runtime_held_span_tests.hthr`.

   One more limit met:
   `close` and `take` take the count as a parameter, since a field read before a
   call and used after it is reflected as read after, and the pin does
   not see that the call leaves it.

   Run by conversion on the block of "abc", the schedule's last word
   and the working variables after the first round are FIPS 180-4's
   (`sha256_compression_tests.hthr`); all sixty-four rounds are past one
   conversion's budget, as they are for the span functions.

   **A loop** is built
   (`lib/_tests/native/runtime/runtime_held_loop_tests.hthr`): a
   `mut self` method that `decreases` a word's `toNat` and ends, in a
   tail `if h:`, in its own call.

   - *Theory* (`rt_file_loop.hthr`, "A loop as the passes it counts";
     `rt_held_loop.hthr`). §9.3.
   - *Reflector* (`rt_held_reflect.hthr`). The body is read from the
     function's step (`T::m::body`, the recursion a parameter), and its
     own call is the walk's end as a call is: the record settled, the
     operands made, `FTm::Again`.
   - *Generator* (`runtime.hthr`, `runtime_held_counted`). The pass is
     written out as a function of the passes after it and the compiled
     function is `FFun::rounds` of it; that the pass is the body
     (`FFun::Passes`) is by computation at every callee. Two statements
     that read the iteration through other definitions (the link's
     answer, and the iteration as a meaning) are proved with the
     iteration a parameter and read at it (`HWorld::at`): compared at
     the iteration itself, the kernel unfolds a pass on one side before
     the other side arrives at the iteration, and once that side has
     passed more heads than the kernel keeps (`Passed::KEPT`) the two
     meet only at the count's end.

   A loop calls other functions of the record, and a function calls a
   loop, each by the other's theorem. Not taken: a self-call that is not
   the end, and a loop whose ending arm stores into the record (the
   `decreases` companions are not made for that shape,
   `issues/decreases-no-companions-ending-arm-store.md`).

   **A function that only reads the record** (`self t: T`, answering a
   word) is built, loops included (`Tally::count_up`, `Tally::add_up` in
   the loop probes; `PortMap::find_at`, a hash table's lookup, in
   `runtime_ports_tests.hthr`). What it publishes is the writer's
   statement at its word beside the record as it was:
   `T::m::runs_held(own, t, length, …, holds) : Agrees(whole, length,
   HWorld::unchanged(t, T::m(t, …)), T::m::bytes(own, length, …))`, so
   `.value` is the agreement of the word and `.holds` says the span
   still holds `t`. Its code is a writer's that stores nothing.

   - *Theory* (`rt_held_loop.hthr`, "A loop that only reads the
     record"). A reader's step answers a word, so its body is pinned to
     it read for the value: `FFun::HeldReads`, the body's held meaning
     with `done` the end's `.value` and the self-call answered by a
     word, is the step by conversion as a writer's body read whole is.
     `FFun::reads_guarded` turns that into the writer's equation
     (`FFun::HeldGuarded`) at `HWorld::unchanged`, once: a body with no
     store, call, lend or loop node (`FTm::still`, decided by
     evaluation) ends at the record it began at or goes round on it
     (`FTm::still_keeps`), and a pass that goes round reads every
     answer alike at its state, so that state is below the measure
     (`FFun::falls_value`), where the answer is the function's beside
     the record. `FFun::counted_held` then applies unchanged.
   - *Reflector.* A reader's arm that is neither a branch nor its own
     call is its value beside the record as it was (`rt_held_tail`'s
     `reads`).
   - *Generator* (`runtime_held_counted`). The function's equation is
     opened at its word, with the same binders and the same proof from
     `ext` and `irrel`, and wrapped by `reads_guarded`.

   Not taken: a reader loop that calls another function of the record
   (`FTm::still` refuses every call, which a reader's call would not
   need).

   **A call of another function of the record** is built
   (`lib/_tests/native/runtime/runtime_held_call_tests.hthr`). `t.m(x)`
   in a `runtime fn` of `T`, at a `runtime fn T::m(mut self t: T, …)`
   declared before it, is a call of the callee's code over the span:

   - *Theory* (`rt_held.hthr`). A computation's mark may be a held
     function, `Runs(words, run)`: its function of the record at the
     words it takes. A caller's held meaning then names `T::m` and never
     its code, so the caller's pin is still a conversion over the
     record. What the mark owes (`HWorld::Runs`) is the callee's
     agreement, the statement its own `runs_held` is.
   - *Reflector* (`rt_held_reflect.hthr`, "The walk"). The elaborator
     hands a body over with every binding substituted: a call stands
     wherever its record or its word is read. The walk reads the order
     back: a record is settled when the span holds it, a call is made
     once the record it takes is settled, and the stores of a record are
     made last before the call or the end that needs it. Before each
     call it makes the reads of the record that the body uses after it,
     so a value of the record as it was can be used after a call.
   - *Generator* (`runtime.hthr`). The callee's promise is its
     published theorem at the words the operands are, read along the
     call as the caller's world makes it; that the world's call is the
     callee applied is proved with the callee a parameter, since at the
     callee itself the kernel advances the newer head, which is the
     callee, through its whole body before the world's table arrives at
     its name. `T::m::bytes` is published beside `T::m`
     (`HWorld::of_record`), and the linker reads there whose tables a
     callee's are.

   A caller's program is its callee's and itself. **A callee that only
   reads the record** is called as a writer is (probes `Tally::peek`,
   `Tally::sum_get`, `Tally::set_get`): its code over the span, its word
   bound where a value reads the call (the reflector's `st.handles`),
   and the record the span holds left as it was, so it is not among the
   calls that changed it. Its mark is `Runs` at its word beside the
   record as it was, which is what its `runs_held` states. Not taken yet:
   what the issue lists.
5. Later, each its own issue: padding-preserving `put`; loads and stores
   wider than a byte; the comparisons a known size makes unnecessary.

## 10. Functions as fields: classes, and a layout as data (2026-11-12)

Minus, on §5 and §6 as built: "I'm unsure on the amount of functions as
fields though I'm unsure of an obvious best way", then, asked what the
function records are good for, "why aren't they typeclasses then?" This
section is what a prototype showed about both answers. Nothing here is
in the library yet. The prototype's files check against the library as
it stands and are kept in the project's shared folder
(`layout-prototype/`: `shape.hthr`, `shape_tests.hthr`, `laidv.hthr`,
`rec.hthr`, `cls.hthr`, `cls2.hthr`).

### 10.1 What the function records are, and where they stop

`Stored<A>` and `Part<A, B>` are records of functions with their laws.
That is the right *meaning*: a codec is a way to read, a way to write
and laws, anything that keeps the laws is one (a varint, a `Bool` in a
byte), and the laws are proved once for all of them. It is the wrong
thing to *hold*. A function is opaque, so every reader that needs to
know what a codec is made of (the declaration, a rule that chooses the
field order, the generator that emits a field access) evaluates one
number at a time or matches on a spelling, and at run time a record of
functions is closures, which the compiled language does not have and
should not gain for this.

Run time needs numbers (`Layout`, §3 and §4) and, for a field access, a
load of a known width at a known offset. Neither is a call of `read`.

### 10.2 Two classes

A class is still a record of functions. What it changes is who picks the
value: resolution, at compile time, from a closed term. Two associations
here are canonical enough to be classes, and both were being done by
name.

**A codec to its compiled accessor**, keyed by the codec's term as
`Compile(f)` is keyed by `f`:

```heather
class Wide<A>(codec: Stored<A>) { bytes: Nat, sized: codec.layout.size = bytes }
instance Wide<BitVec(32)>(Stored::u32_be()) { bytes := 4, sized := refl }
instance Wide<BitVec(32)>(Stored::u32_le()) { bytes := 4, sized := refl }
fn width<A: Wide(codec)>(codec: Stored<A>) → Nat { A.bytes }
```

Checked (`cls2.hthr`): two instances at one type are told apart by the
codec's term, the instance is found from the codec passed, and a codec
with none is refused as "no instance".

**Built** as `Accessor<A>(codec)` (`lib/native/runtime/stored_accessor.hthr`):
the word a value is held as (`wide`, `narrow`, and that a value is kept
by its word), the `runtime fn` that reads the codec's value and the one
that stores it, and the two theorems that tie them to `get` and `put`
under a length word. Instances for `Stored::u32_be()` and
`Stored::u64_be()`, which are the words that have compiled code
(`stored_words.hthr`). Over it, the laws at a part of what a span holds
for every codec with an accessor (`Stored::read_at_part`,
`Stored::write_at_part`), which are the four width-specific theorems of
`stored_words.hthr` as one pair. Stage B's reflector (§9.4) finds a
field's load and store by resolution. It is open: a new codec comes with
its accessor and the generator does not change.

**A declared type to its layout**:

```heather
class Lay<T> { laid: Laid<T> }
fn size_of<T: Lay>() → Nat { T.laid.shape.layout().size }
instance<A: Lay, B: Lay> Lay<Pair<A, B>> { laid := A.laid.then(B.laid) }
```

Checked (`cls.hthr`): an instance for a record, the pair's derived from
its parts', `size_of<Pair<Header, Header>>() = 32` and the bytes written
by `refl`, a `read_at<T>` and `write_at<T>` of any laid type with their
law from the codec's, and `size_of<Nat>()` refused. `laid record T`
would declare the instance, and a field of type `R` is then found by
resolution where the generator now looks up the name `R::stored`.

What stops it short: **an instance is keyed by its class and its
carrier's head**, so `BitVec(8)`, `BitVec(32)` and `BitVec(64)` cannot
each have one (`docs/elaborator/instance-resolved-key-design.md`). Words need one
instance at every width, which wants a codec of a `BitVec(n)` at any
`n` (whole bytes, the value resized). That codec is not the library's
`Stored::u32_le()` by conversion at 32, so the words' theorems would
need restating over it, or the instance has to choose by cases on the
width. Open. Byte order is the other limit: an instance is one order,
the machine's, and a declaration that wants another names it, as now.

### 10.3 A layout as data: `Shape`

```heather
inductive Shape { Byte, Bytes(k: Nat, order: Endian), Aligned(of: Shape, log: Nat),
                  Array(of: Shape, n: Nat), Then(a: Shape, b: Shape), Padded(of: Shape) }

fn Shape::Holds(self s: Shape) → Type              // u8, BitVec(8 * k), [A; n], Pair<A, B>
fn Shape::layout(self s: Shape) → Layout           // plain numbers, no proof in sight
fn Shape::stored(self s: Shape) → Stored<s.Holds()>
theorem Shape::stored_layout(self s: Shape): s.stored().layout = s.layout()
```

A shape is the codec combinators with the functions taken out: one
constructor per combinator, and `Shape::stored` applies them, so no law
of a codec is proved again. It is plain data, so a program can build
one, compare two, sort a list of them by alignment and hold one at run
time. `Shape::u32(BigEndian).stored()` is `Stored::u32_be()` by
evaluation.

A place inside a shape is data too:

```heather
inductive Path { Here, Inside(rest: Path), First(rest: Path), Second(rest: Path), Item(i: Nat, rest: Path) }

fn Shape::at(self s: Shape, p: Path) → Option<Shape>     // the shape at the path
fn Shape::offset(self s: Shape, p: Path) → Nat           // where it begins
record Found(s: Shape, p: Path) {
    shape: Shape,
    part: Part<s.Holds(), shape.Holds()>(s.stored()),
    names: s.at(p) = Some(shape),
    stores: part.codec = shape.stored(),
    lies: part.offset = s.offset(p),
}
fn Shape::find(self s: Shape, p: Path) → Option<Found(s, p)>
fn Shape::found(self s: Shape, p: Path, has: s.Has(p)) → Found(s, p)
```

`at` and `offset` are the cheap readings. `find` walks the path
composing §5.3's parts and returns, beside the part, that it is of the
shape `at` names, stores it by that shape's codec and lies where
`offset` says. `s.Has(p)` is a closed fact at a closed shape and path,
so a caller writes `s.found(p, trivial)` and a path that is not there is
refused where it is written. Checked on SHA-256's context as a shape:
its sixth schedule word is at 84, and reading it through the part is
`vector_index(v.fst.snd, 5, trivial)`, by `refl`.

Three choices, each found by trying the other first:

- **Wrappers are steps of the path** (`Inside` through `Aligned` and
  `Padded`). With wrappers transparent, `offset` and `at` matched on the
  shape before the path, and every proof about an open path was stuck
  on which came first.
- **`find` is a function to an option, not an indexed family of valid
  paths.** A family `Path(s, t)` would make an ill-formed path
  unwritable, and is where the elaborator is weakest (indices that are
  computed types). The option costs one `trivial` at a closed path.
- **What `find` returns carries its laws** (`Found(s, p)`) instead of
  separate theorems about `find`. A theorem about a function that
  matches on two arguments and maps under an option has to redo the
  matching; the record is built where the facts are in hand.

**A record as one value** (`laidv.hthr`):

```heather
record Laid<T> { shape: Shape, of: shape.Holds() → T, to: T → shape.Holds(),
                 back: (t: T) → of(to(t)) = t, forth: (p: shape.Holds()) → to(of(p)) = p }
fn Laid::stored<T>(self l: Laid<T>) → Stored<T>
fn Laid::part<T>(self l: Laid<T>, p: Path, has: l.shape.Has(p)) → Part<T, l.shape.found(p, has).shape.Holds()>(l.stored())
fn Laid::value<T>(self l: Laid<T>) → Part<l.shape.Holds(), T>(l.shape.stored())
```

A record carries exactly the two functions that have no first-order
form, its constructor and its projections. The codec, the layout and
every field's part with its laws are library functions of that value
and a path. Checked: a header with padding, a record inside a record
whose field is read as the inner record (`Laid::value`, over a new
`Part::through`, the other direction of `Part::mapped`), offsets, `of`,
`with` and the field's codec by `refl`, and a path that is not there
refused.

What is not a shape: a codec given as a term (an arbitrary `Stored<A>`
has no description), a type that does not use every byte pattern, and a
size that depends on bytes read. `Stored` does not have the last one
either.

### 10.4 What each is for

| Reader | Needs | From |
| --- | --- | --- |
| a proof about a field | laws | `Stored`, `Part` (as built) |
| the generator, for a field's load and store | the accessor of a codec | the accessor class |
| the declaration, for a field of type `R` | `R`'s layout | the layout class, or `R::stored` by name as now |
| a rule that chooses the field order | each field's alignment | `Stored`'s `layout`, which is data already |
| compiled code that lays memory out | sizes and offsets | `Layout` (§4) |
| a program that holds a format, or a field as a value it passes | a description | `Shape`, `Path` |

So the classes cover what the shape was first proposed for, in the open
form, and the shape is what only data can do: the last row. Asked of
Minus as a decision. The recommendation: the accessor class with stage
B's reflector (§9.5 round 3), the layout class once words have their
instance, and the shape left as this checked prototype until a program
needs to hold a layout.
