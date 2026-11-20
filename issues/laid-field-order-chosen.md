---
title: laid record: the declaration chooses where the fields lie, by a rule that is not the written order
status: open
labels: [native,layout,design]
area: heather-in-heather
created: 2026-11-12
updated: 2026-11-20
---

`laid record T { … }` (`lib/std/machine/laid.hthr`, `docs/native/layout-design.md` §6.2) places a record's fields in the order they are written. Minus decided (2026-11-12) that this is not the rule: reordering "should be "magical" by whatever setup the `laid` uses", "the ability for compiler to decide is valuable, though we don't need complex reordering yet", and it is "something to have an issue for". This is that issue.

What is built toward it: the declaration takes `order`, `AnyOrder` by default and `AsWritten` for C's rule, and the note says nothing may read an offset off the source (it is `T::f_part().offset`). Today both orders are the written one, so the freedom is stated and not yet used. SHA-256's context says `AsWritten` because its functions' bodies write the offsets out.

A first rule, and what it needs:

- **The rule**: the fields by descending alignment, ties in written order. With power-of-two alignments it leaves no padding between fields, which is what Rust's default does in effect.
- **Each codec's alignment as a numeral in the generator**: `fields` of the codec to its `layout`, then to `align_log`, `whnf`, and a view that is a literal. A codec whose alignment does not evaluate (an open one) keeps the written order.
- **The permutation in two places**: `to` and `from` of `Stored::record` are written from the constructor's order and the layout's order, which today are the same list. The parts are by name and do not change.
- **Nothing to prove**: a part's laws do not mention where it lies.

What it opens, none of it needed now: a rule as an argument (a function over the table of fields, which is the `docs/native/datarepr-design.md` §5.2 "layout is DATA" reading), rules that read use (fields a loop touches together placed together), and the compiler choosing with what it knows, which is the case Minus named for keeping the choice with the declaration. A first-order description of a layout ([[layout-first-order-description]]) would make each of these a function over data and not over terms.

Done when: `laid record` under `AnyOrder` places fields by a rule that is not the written order, the probes state offsets only under `AsWritten` or through the parts, and a record with a `u8` before a `u64` is shown to lose its padding.

## Log

- 2026-11-12: **SHA-256's context is unpinned (PR #551, 2026-11-12).** Its bodies name `Sha256::…_at` and its theorems are stated at the names, so it is the first record a rule could move. Two things the rule can now use: `numeral(e)` gives the generator a codec's alignment as a number where `whnf` was out of budget (the second bullet above no longer needs the view of a literal), and the published `T::f_at` words are what compiled code follows. What still pins today's order, and would have to be respelled by name when a rule lands: the probes `hash_at_today` to `size_today` in `sha256_context_tests.hthr`, the two numerals Rust is given (`SHA256_CONTEXT_BYTES`, `SHA256_DIGEST_AT`, each a `refl` theorem that fails first), and the literals in `crates/linked/tests/sha256.rs` behind `the_context_lies_where_these_tests_read_it`.
- 2026-11-20: Survey docs/surveys/layout-rewrites-survey.md §3.2: Isomer's commute/assoc steps are this issue's 'nothing to prove' made general (a permutation reconstructs by its inverse).
