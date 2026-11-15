---
title: A let tested by a plain if in a measured loop leaves the let's variable free in the companions
status: closed
labels: [elaborator,decreases,runtime-fn]
area: heather-in-heather
created: 2026-11-15
updated: 2026-11-15
---

A measured loop that binds a value with `let` and then tests it with a
plain `if` around the recursive call had no `f::unfold`/`f::ext`, so a
`runtime fn` written that way was refused with "`f::ext` is not in scope":

```heather
runtime fn ascii_from(span: List<u8>, length, i, left: u64) → u64 decreases left.toNat() {
    if h: 0 < left {
        let b = span.byte_within(length, i).zero_extend(56);
        if b < 128 { ascii_from(span, length, i + 1, left - 1) } else { i }
    } else {
        i
    }
}
```

The companions' walk substitutes a `let` into the body (`inline_lets` in
`crates/elab/src/measure.rs`), but `subst` leaves type arguments alone, and
a plain `if` is a `match` on `decide_bit<b < 128>`: the proposition is a type
argument, so `b` stayed in it with the `let` gone. `f#ext` was then refused
(`<` has no meaning: its carrier is an unknown name), which a reference to
`f::unfold` reports.

Met writing the UTF-8 validator demo (`examples/utf8/utf8_check.hthr`).

## Log

- 2026-11-15: Fixed: `inline_lets` substitutes into the type arguments of
  the body it returns too. Probe `ascii_from` in
  `lib/_tests/native/runtime/runtime_lent_tests.hthr` (refused before the
  fix, certified after).
