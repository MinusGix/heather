---
title: Develop fixed-width bitvectors and their arithmetic proof kit
status: open
labels: [stdlib,mathematics,design]
created: 2026-08-25
updated: 2026-08-25
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
