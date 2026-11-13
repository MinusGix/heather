---
title: A measured runtime fn that only reads is refused by the kernel when its exit calls on a call
status: open
labels: [native,runtime-fn,performance]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-12
updated: 2026-11-12
---

Found probing [[runtime-link-compares-functions]] (2026-11-12). A measured `runtime fn` that only reads its span, and whose exit calls a function with an argument that is itself a call, is accepted by the generator and then refused by the kernel:

```heather
runtime fn probe_past(ctx: List<BitVec(8)>, cn, i: BitVec(64)) → BitVec(64) decreases BitVec::ofNat(64).sub(i).toNat() {
    match h: i.unsigned_lt_bit(BitVec::ofNat(64)) {
        False => sha256_t2(sha256_word_at(ctx, cn, i), i, i),
        True => probe_past(ctx, cn, i.add(BitVec::ofNat(1))),
    }
    on ?dec1 := { let below = bitvec_omega::unsigned_true(64, i, BitVec::ofNat(64), h); bv_omega };
}
```

> error: the kernel rejected `probe_past::compile`: OutOfFuel

(`sha256_t2` is `lib/native/crypto/sha256_round.hthr`'s, `sha256_word_at` `sha256_block`'s: four bytes of the span as a word.)

## What moves it

With the same loop and only the exit changed:

| exit | verdict |
|---|---|
| `sha256_word_at(ctx, cn, i)` (a callee of the loop's own type) | passes |
| `sha256_k(i)` (the 64-leaf tree) | passes |
| `sha256_t2(i, i, i)` | passes |
| `sha256_t1(i, i, i, i, i, sha256_word_at(ctx, cn, i))` (the call where `T1` uses its argument once) | passes |
| `sha256_t2(i, sha256_word_at(ctx, cn, i), i)` (where `T2` uses it twice) | passes |
| `sha256_t2(sha256_word_at(ctx, cn, i), i, i)` (where `T2` uses it eight times) | out of fuel |
| the same with the call `let`-bound first | out of fuel |
| a plain reader of the loop's type that is `T1` over five words of the span, called with variables | out of fuel |

And around it:

- A parameter of padding on the loop, so that its type differs from every callee's, changes nothing: this is not the link pairing of [[runtime-link-compares-functions]].
- A **plain** reader with the same body as the failing exit passes, with the same type as its callee or another.
- A measured **writer** with heavier calls passes: `sha256_expand` calls `sha256_next` on four words read from the span, each used more than once, and `sha256_rounds` calls the whole round.

So the cost grows with how many times a callee uses an argument that is a call, and it does so transitively (the last row passes only variables, and its callee's body holds the calls): somewhere in the measured reader's instance the kernel is comparing callee bodies unfolded, with each copy of the argument compared on its own, where a plain instance and a writer's compare the calls as calls. The generator's own budgeted check of the same instance passes, so the two conversions take different routes here.

Not located. The place to look is what `Setup::compile_measured` is given: `guarded`, the function's unfolding equation against `Fun::Guarded` through `Setup::guarded_spans`, where [[runtime-measured-instance-conversion-budget]] moved a comparison once already; and a kernel trace of the same-head attempts in `Conv::tm_w`, which is how the link pairing was found (a counting build, `HEATHER_LADDER`, logs only the host's failures today, not the gate's: [[conversion-fuel-failure-says-where]]).

## Why it matters

Nothing checked in needs it: SHA-256's compress is writers throughout, and the lexer's loops pass. It is a wall a reader over a span meets as soon as its loop ends in arithmetic on what it read, which is what a checksum or a parser's finish is.

## Done when

The function above is a `runtime fn`, and the table's rows all pass, at a cost that is a sum over the calls and not a product over the uses.

## Log

- 2026-11-12: The callee named `sha256_word_at` above is now `List::u32_be_within` (`lib/native/runtime/stored_words.hthr`), so the reproduction reads `ctx.u32_be_within(cn, i)` where it says `sha256_word_at(ctx, cn, i)`. Nothing else about the case changed.
