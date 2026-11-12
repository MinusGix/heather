---
title: A layout as first-order data beside Stored and Part, so that a record publishes one description and not a function per field
status: open
labels: [native,layout,design]
area: heather-in-heather
created: 2026-11-12
updated: 2026-11-12
---

Minus, on the layout library (2026-11-12): "I'm unsure on the amount of functions as fields though I'm unsure of an obvious best way." Read here as two things, which is my reading and not his words: `laid record T` publishes one function per field (`T::f_part()`), and `Stored<A>` and `Part<A, B>` are themselves records of functions (`read`, `write`, `of`, `with`) with their laws.

What they are good for: a codec is exactly "a way to read and to write, with laws", so anything that satisfies the laws is one, and the combinators (`then`, `array`, `padded`, `map`) are proved once. What they cost: a function is opaque. Nothing can ask a `Stored<A>` what it is made of, so the declaration reads codecs off types and off terms, a rule that reorders fields ([[laid-field-order-chosen]]) has to evaluate alignments one at a time, a generator that emits a field access for a `runtime fn` has to recognise `Stored::u32_be()` by its spelling, and each field is a declaration of its own because nothing holds the fields as a table whose entries have different types.

The usual answer is a description beside the functions, first-order:

```heather
inductive Shape { Byte, Word(bytes: Nat, order: Endian), Array(of: Shape, n: Nat), Then(a, b: Shape), Padded(of: Shape), Aligned(of: Shape, log: Nat) }
fn Shape::Holds(self s: Shape) → Type          // u8, BitVec(8 * k), [A; n], Pair<A, B>
fn Shape::layout(self s: Shape) → Layout       // by recursion, a numeral at a closed shape
fn Shape::stored(self s: Shape) → Stored<s.Holds()>
inductive Path { Here, Fst(p: Path), Snd(p: Path), At(i: Nat, p: Path) }
fn Shape::part(self s: Shape, p: Path, ok: s.has(p)) → Part<s.Holds(), s.at(p).Holds()>(s.stored())
```

`Stored` and `Part` stay what a codec and a field are; a `Shape` is a name for the ones built from the combinators, and its `stored` and `part` are those combinators applied, so no law is proved again. A record is then one value: its shape, the map to and from the record, and a table of field names to paths. One function per field becomes sugar over that table, or goes.

What it would buy: the declaration, a reordering rule, the runtime generator (which code reads a `Word(4, BigEndian)` at an offset is a function of the shape) and run-time layout code (`docs/layout-design.md` §4: a shape is data a program can hold) all read one description. What it costs: a type computed by recursion (`Shape::Holds`) in every statement about a field, which is where the elaborator is weakest ([[type-level-reduction-over-computed-operands]], [[vector-literals-at-computed-carriers]]); `map` has no first-order form, so a record's own type is still reached through its constructor; and a type with a validity invariant (a `Bool` in a byte) fits neither this nor `Stored` yet.

Not built. Recommended before stage B's generator is written (`docs/layout-design.md` §6.2), because that generator is the first reader that needs to take a codec apart, and it would otherwise match on spellings.

Done when: either a `Shape` with `Holds`, `layout`, `stored` and `part` exists and `laid record` publishes one, with the probes of `laid_tests` restated over it, or this is closed with the reason the functions stay as they are.
