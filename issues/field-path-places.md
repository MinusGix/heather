---
title: A field path is not a place: x.f := e and x.f.m(a) on a mut self method are refused
status: open
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

- `x.f := e` is `x := x with { f := e }` (or the constructor applied to the other fields' projections, whichever the record surface gives), and `x.f.g := e` nests.
- `x.f.m(a);` for a `mut self` method `m` is `let #m = x.f.m(a)` read as the call's record, then `x.f := #m.after`, its value `#m.value`: the local rule with the store going through the path.

To settle: what the refusal says for a path through something that is not a record field (an index, a call); whether a path through a `datarepr`'d or one-field record costs anything at run time (it should not: record η makes the rebuild the identity on the other fields).

## Done when

`Hash::poke` above elaborates, with `.after` probes at a neutral receiver in `lib/_tests/std/core/imperative_statements_tests.hthr` (a field assigned, a method called on a field, a nested path, and a refused path through a call).
