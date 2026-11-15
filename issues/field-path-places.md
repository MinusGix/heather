---
title: A field path is not a place: x.f := e and x.f.m(a) on a mut self method are refused
status: closed
labels: [frontend,imperative,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-11-12
updated: 2026-11-12
---

A field of a mutable local is not a place: it cannot be assigned, and a `mut self` method cannot be called on it (2026-11-12).

```heather
record Hash { bytes: List<u8>, count: u64 }

fn Hash::poke(mut self ctx: Hash, cn, i: u64) → u64 {
    ctx.bytes.put_within(cn, i + 64, 0);
    ctx.count := ctx.count + 1;
    i
}
```

> error: parse error: only a local is assigned: write `x := e` (a field path, `x.f := e`, is not supported yet)

> error: `put_within` is a `mut self` method, so it updates its receiver, and nothing here keeps the update: call it on a `let mut` local of this function's own blocks, …

[[pure-imperative-statements]] planned `:=` "also to field paths, via `with`" and built the local case. The method call is the half a type that wraps another needs: a record whose field is a span of bytes can only update that span by rebuilding itself by hand, `ctx := Hash(List::put_within(ctx.bytes, …).after, ctx.count)`, which is what stands between `lib/native/crypto`'s methods on `List<u8>` and methods on a context type of its own ([[sha256-context-type]]).

## Proposed

A place is a mutable local followed by field names. Both forms lower in the parser, where `:=` and the method-call candidates already do (`crates/syntax/src/imperative.rs`):

- `x.f := e` is `x := x with { f = e }`, and `x.f.g := e` nests.
- `x.f.m(a);` for a `mut self` method `m` is `let #m = x.f.m(a)` read as the call's record, then `x.f := #m.after`, its value `#m.value`: the local rule with the store going through the path.

To settle: what the refusal says for a path through something that is not a record field (an index, a call); whether a path through a `datarepr`'d or one-field record costs anything at run time (it should not: record η makes the rebuild the identity on the other fields).

## Done when

`Hash::poke` above elaborates, with `.after` probes at a neutral receiver in `lib/_tests/std/core/imperative_statements_tests.hthr` (a field assigned, a method called on a field, a nested path, and a refused path through a call).

## Log

- 2026-11-12: Built on PR #551 (docs/language/sequencing-surface-design.md §20). A place is a mutable local followed by field names. `x.f := e` is written by the parser as `x := x with { f = e }` (`place_update`), nesting for longer paths. `x.f.m(a)` is a candidate of the local `x`, claimed as `x.m(a)` is; the elaborator rebinds `x` to `x with { f = call.after }` when `m` returns `Mutated` and reads an ordinary call when not, so a call such as `x.items.len()` leaves `x` untouched. The `decreases` companions follow the receiver through a path (`inline_lets`), which needed the walk's substitution to read record updates and literals. Also fixed on the way: a tail arm that is a bare call on the receiver (`True => c.tick(1),`) was refused where the same arm as a block worked. Probes: `Tally::bump`, `Board::deep`, `Tally::count`, `Tally::maybe`, `swap_in` at an open type and three refusals in `imperative_statements_tests`; `Ledger::fill` with its unfolding equation in `decreases_unfolding_tests`; a parser test. `Hash::poke` and a measured `Hash::zero` over `ctx.bytes` elaborate. Not built: a path through an index, and any run-time meaning (a record has no runtime layout; [[sha256-context-type]]).
