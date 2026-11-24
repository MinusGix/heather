---
title: Laid records that take parameters, arrays sized by a word, and little-endian accessors
status: open
labels: [native,runtime,layout]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-24
updated: 2026-11-24
---

A `runtime fn` can hold a span of bytes with a run-time count (`Bytes(n)`)
and a laid record whose arrays have a count the type fixes, but nothing
in between: `laid` takes only a record with no parameters ("`Limbs` is not
a type with no parameters"), and an array parameter `mut t: [u64; 8]` "has
no runtime layout" (ledger row 11, `port_pred_limbs`).

Decided (Minus, 2026-11-24; docs/native/rung2-spans-design.md §3): spans
of anything are a general feature of `laid record`, not a type of their
own.

```heather
laid record Limbs(n: u64)    { w: [u64; n.toNat()] }
laid record Vector(cap: u64) { len: u64, items: [u64; cap.toNat()] }
```

- A parameter the layout depends on is carried at run time as a word
  beside the span's place and length; one that does not reach the layout
  is erased.
- The parameter counts elements; the premise is `size(n) <= length`, the
  size an expression in the parameters.
- The variable array stands last in the first version; offsets are
  layout expressions, so a middle array is a later extension, not a
  redesign.
- Little-endian accessors (`Stored::u32_le`, `u64_le`) so that `laid`'s
  default byte order compiles; big-endian stays an opt-in.

`Stored::array(s, n)` already takes any `Nat`, and the accessor already
reads at a base and count that are words (`Accessor::read_at`), so the new
work is the declaration generator's (parameters and an open-count codec),
the reflector's (the count's word where a literal is today) and the runtime
generator's (the parameter words among the code's operands, `runs_held` at
every value of them).

## Done when

- `port_pred_limbs` is written over `Limbs(n)` and compiles in the ledger,
  with a run by `refl` at two counts and `runs_held` restated at an open
  `n`; an index without a proof is refused with the found-proof message.
- A record with a parameter that does not reach its layout compiles with
  that parameter absent from the code's operands.
- A laid record with the default (little-endian) byte order compiles, and
  a word read from it is the word Rust's `&[u64]` holds at that place.
- A variable array that is not the last field is refused with a reason
  that says so.

Elements that are records (`[Entry; cap]`) and loops over parameterized
records follow (the latter after [[loops-on-one-combinator]]'s round 4).

## Log

- 2026-11-24: 2026-11-24: Reshaped by Minus's decision (docs/native/rung2-spans-design.md §3): no separate Span type; laid records take parameters, the carried ones counting elements, the variable array last at first, little-endian the default.
