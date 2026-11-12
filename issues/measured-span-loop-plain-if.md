---
title: A measured span loop whose test is a plain if has no ext companion
status: closed
labels: [native,runtime-fn,diagnostics]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-12
updated: 2026-11-12
---

A measured `runtime fn` over a span whose test is a plain `if` is refused by the generator with a message about companions (2026-11-12, after #586):

```heather
runtime fn zero_from(ctx: List<u8>, cn, i: u64) → Mutated<List<u8>, u64> decreases (64 - i).toNat() {
    if i < 64 {
        let mut ctx = ctx;
        ctx.put_within(cn, i + 64, 0);
        zero_from(ctx, cn, i + 1)
    } else {
        Mutated(ctx, i)
    }
}
```

> error: `runtime fn zero_from`: the generator failed: `zero_from` cannot be a runtime fn that writes a span: it has no `ext` companion, which a loop's instance is built from: the function's own call is where a `decreases` function's companions do not follow it (docs/decreases-unfolding-design.md)

With the evidence named, `if h: i < 64 { … }`, the same function certifies, and its program is the `match h: i.unsigned_lt_bit(64)` spelling's by `refl` (`lib/native/crypto/sha256_block.hthr`'s loops are written so). The declaration elaborates without `h:` (the measure is discharged from the branch's condition either way), and only the companions differ: as an ordinary `fn` the same body has the access points `rec` and `body` and no `ext` or `unfold`, where the `if h:` spelling has both. Either the plain `if` should get the same companions, or the refusal should say what to write: "name the test's evidence, `if h: i < 64`".

## Done when

`zero_from` above certifies, or is refused with a message that names `if h:`, with a probe in `lib/_tests/native/runtime/runtime_span_tests.hthr`.

## Log

- 2026-11-12: Done: the lifted obligation of a plain `if` had lost the test, so it was refused, the companions were declined, and the generator met no `ext`. The body rewrite gave an equation to a `match` on a computed scrutinee (an AutoEqs candidate, `crates/elab/src/measure.rs`) but not to an `if`, which is the same match on its test's bit; it does now, and the companion walk numbers it in step. `zero_from` certifies, its program is `zero_from_named`'s (the `if h:` spelling) by `refl`, both in `lib/_tests/native/runtime/runtime_span_tests.hthr`. Library re-elaborated (plain `scripts/test`).
