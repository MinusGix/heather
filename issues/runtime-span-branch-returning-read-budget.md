---
title: A span runtime fn whose branch arm returns a read is past the conversion budget
status: open
labels: [native,runtime-fn,performance]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-12
updated: 2026-11-12
---

A `runtime fn` that writes a span, ends in a branch, and has an arm whose value is a read of the span is refused when its instance is built: the pin of the reflection to the function runs out of the conversion budget. Found writing the probes of `lib/_tests/native/runtime/rt_held_tests.hthr` (2026-11-12).

## Repro

With `tally_count` and `tally_total` each `span.u64_be_within(length, <offset>)` and `List::tally_put_count` a `put_u64_be_within` (as in the probes):

```heather
// refused: "`List::v1`'s instance: an argument's type could not be compared with the expected type within the conversion budget"
runtime fn List::v1(mut self span: List<u8>, length: u64) → u64 {
    let c = tally_count(span, length);
    let n = tally_total(span, length);
    if c < n { span.tally_put_count(length, c + 1) } else { c }
}

// refused the same way: the test is one call, the arm without a store returns a read
runtime fn List::v2(mut self span: List<u8>, length: u64) → u64 {
    if tally_room(span, length) < 1 { tally_count(span, length) } else { span.tally_put_count(length, tally_count(span, length) + 1) }
}

// accepted: the arm without a store returns a parameter
runtime fn List::v3(mut self span: List<u8>, length, limit: u64) → u64 {
    if tally_count(span, length) < limit { span.tally_put_count(length, tally_count(span, length) + 1) } else { limit }
}
```

So the arm that returns a read is what the three differ in. Not yet bisected further: whether one side's `FTm::recast` of that arm meets the function's arm at the callee, or the callee is unfolded on one side first (the readers bottom out in eight `byte_within`s, each a stuck `match`).

## Why it matters

A function of a laid record that branches and returns a field in one arm reflects to this shape. The held generator ([[sha256-context-type]], `docs/layout-design.md` §9) would define the function of bytes as the reflection's meaning, so its pin is of the function of the record to the held meaning and never meets this; a function of bytes written by hand does.

## Done when

`v1` and `v2` are accepted, or the refusal names what to write. Related: [[runtime-measured-reader-heavy-callee]], [[conversion-respelled-world-compares-reflection]], [[rt-file-read-before-store]] (the other thing a hand-written function over field accessors meets: a read bound before a store and used after it is refused).
