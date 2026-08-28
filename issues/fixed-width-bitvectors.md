---
title: Develop fixed-width bitvectors and their arithmetic proof kit
status: closed
labels: [stdlib,mathematics,design]
created: 2026-08-25
updated: 2026-08-28
---

Heather has unbounded `Nat` and `Int`, kernel vectors and `Fin`, and useful
arithmetic/order kits, but no public carrier for an exactly `n`-bit value.
Compiler IRs, binary formats, hashes, protocol fields, and machine models all
need the same operations and the same proofs.  An x86 model is the forcing
customer, not the owner: wrapping addition, carry, slicing, and extension must
not be redefined inside an architecture module.

Choose the representation by writing a small real API.  The leading candidate
is a width-indexed vector of bits, but compare it with a bounded `Nat`
presentation before committing.  Score the choice on computation at an open
width, extensional equality, indexing/updating, arithmetic proofs, conversion
to/from `Nat` and `Int`, and the cost of stating common fixed widths.  Do not
add a primitive kernel former merely to make the first implementation short.

The generic operations must not bake in x86 policy.  In particular, a shift
operation accepts the count it mathematically means; an instruction model is
responsible for masking or otherwise interpreting an architectural count.
Likewise expose carry/borrow and signed overflow as reusable results or lemmas,
not as names owned by a flags register.

## Acceptance

- Select and document `BitVec(n)`'s representation, bit order, equality, and
  the relationship between width zero and nonzero widths.
- Provide construction, indexing/update, extensionality, zero/one/all-ones,
  bitwise complement/and/or/xor, truncation, zero/sign extension, slicing,
  concatenation, and split/concat laws.
- Provide unsigned and signed comparison, wrapping add/sub/neg/mul, shifts,
  and reusable carry, borrow, and signed-overflow characterizations.
- State the modular arithmetic boundary explicitly: which operations agree
  with `Nat`/`Int` under interpretation and which reduce modulo `2^n`.
- Prove enough algebra and conversion laws to establish, at minimum,
  xor-self, add/sub cancellation modulo the width, extension/truncation laws,
  read-after-bit-update, and the carry/overflow formulas used by a scalar ALU.
- Exercise widths 0, 1, 8, 16, 32, and 64 plus one neutral width.  Closed
  numeral tests alone are not acceptance.
- Record any language/API refusal encountered rather than encoding around it;
  those refusals are the dogfooding output of the round.

Division, remainder, population count, and specialized wide multiplication
are follow-ons.  The initial kit should leave coherent homes for them without
waiting for them.

## What it assumes from elsewhere

- **[[surface-fin-indexing]]** owns surface `Fin(n)` and vector indexing.  This
  issue assumes those forms are available candidates, not that vectors have
  already been selected as the representation.
- **[[termination-measures]]** owns non-structural recursion support.  This
  issue does not disguise division/remainder as fuelled bitvector operations.
- **[[carrier-directed-numerals]]** owns how literals select a carrier.  This
  issue owns bitvector construction and interpretation even if `3 : BitVec(8)`
  is initially unavailable.

## Log

- 2026-08-25: Filed from the x86-64 model audit.  The demanded API is generic
  because fixed-width arithmetic is also a compiler, format, crypto, and
  data-representation foundation.
- 2026-08-25: LANDED in `lib/std/bitvec.hthr`, with acceptance coverage in
  `crates/elab/tests/lib_std_bitvec.rs`. `BitVec(n)` is a one-field record over
  the kernel vector `[Bool; n]`, least-significant bit first. The wrapper is
  representation-transparent in the ordinary Heather sense: it contains no
  bound proof and equality is structural equality of its `bits` field.
  `BitVec(0)` is the singleton empty vector; its sign bit is canonically false,
  and zero-width construction and arithmetic discard their inputs.

  The API includes construction and interpretation, indexed read/update and
  extensionality, the pointwise Boolean operations, bounded slicing,
  concat/split, truncation and both extensions, unsigned and two's-complement
  signed order, wrapping arithmetic, mathematical-count shifts, carry/borrow,
  and signed-overflow formulas. The modular boundary is stated in the module
  header and reflected in the implementation: `ofNat`, add, sub, neg, and mul
  wrap, while `toNat`/`toInt` interpret. Increment/decrement are structural
  inverses, which makes add/sub cancellation provable at an open width rather
  than merely tested on numerals. The other minimum laws are likewise open:
  xor-self, read-after-update, extensionality, split/concat projections, and
  extension/truncation.

  DOGFOODING REFUSAL ([[vector-types-as-expressions]]): the initially preferred spelling
  `fn BitVec(n: Nat) -> Type { [Bool; n] }` is not writable. In a type-valued
  function body the expression parser commits prefix `[` to a vector literal
  and reports `expected ] (vector literal), found Semi`; expected-universe
  information does not select vector-type syntax. A one-field value-indexed
  record preserves the selected vector representation without inventing a
  bounded-`Nat` proof carrier or adding a kernel former. The refusal is left
  recorded here rather than repaired as an unrequested parser round; the
  linked issue now owns that surface-language oversight.

  Tests cover widths 0, 1, 8, 16, 32, and 64, plus a neutral width; computation
  spans bit order, conversion, wrapping arithmetic, overflow, shape operations,
  extension, and shifts, while separate probes apply every core law to open
  values and widths and carry negative controls.
- 2026-08-26: The first executable x86 `ADD` customer added the missing
  Boolean view `carry_add_bit`, implemented as a structural ripple rather than
  by deciding the arithmetic `carry_add` proposition through `Nat`. The latter
  route attempted open `2^64` comparisons and exhausted the test-process memory
  rail. Closed carry/no-carry controls landed; the open correspondence theorem
  is owned by [[bitvec-executable-carry-correspondence]].
- 2026-08-26: [[bitvec-executable-carry-correspondence]] closed: the structural
  ripple result is now proved equivalent to the unsigned arithmetic carry
  proposition at an open width, in both directions. The proof also replaced
  `toNat`'s open `2 * tail` spelling with propositionally equal structural
  doubling, giving binary proofs a reduction shape proportional to width.
- 2026-08-28: The executable x86 decoder added `bitvec::eq_dec`, a structural
  equality decision at an open width with positive and negative evidence. It
  is called directly: registering `Decide<x = y>` cannot recover the width
  binder from the instance head under the existing binder-occurrence rule.
