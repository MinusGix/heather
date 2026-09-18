---
title: Comparing two lazily unrolled Nat recursions on a literal at a stuck argument descends the literal
status: open
labels: [kernel,conversion,perf]
created: 2026-09-18
updated: 2026-09-18
---

Found closing [[utf8-decode-conversion-blowup]] (2026-09-18).

A Nat recursion on a **literal** whose other argument is **stuck** —
`nat::leb(0x800, code)` at a neutral `code`, or `char::is_scalar(code)`'s
`leb(0xD800, code)` — evaluates lazily and cheaply: `elim_Nat` on a
`NatRun` whose fold does not accelerate (the counter it would synchronize
with is a neutral, not a run) applies the step once, with the induction
hypothesis a *pending* elimination of the run's predecessor. But the
result is a closure chain as deep as the literal, and **conversion of two
such chains descends it level by level**: the `ElimNat` neutral arm
compares the step closures under pushed binders, the step applies the
pending hypothesis to the fresh local, that forces the next level, and so
on — one `Conv::tm` frame and ~90 fuel units per level, measured with a
depth trace. Two copies of `leb(0x800, …)` need 2048 frames against the
native depth budget of 1024 (`OutOfFuel`, or a worker stack overflow at
width eight); two copies of `is_scalar(…)` need more fuel than the budget
holds.

The chains are only compared when the δ-lazy stage failed to meet above
them. After [[utf8-decode-conversion-blowup]]'s fix that no longer happens
on the *positive* statement (both sides meet at the glued `leb` spine), but
it still happens whenever a **bare-application meet fails honestly** and
both sides are unfolded to their δ-heads through such a recursion:

```heather
// wrong class: decode_seq(C2, …) against decode's C3 arm.
theorem bad(q: BitVec(4), r, s: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead3_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), t))))
        = push_char(decode_seq(C2, lead3_byte(q),
              Cons(cont_byte(r), Cons(cont_byte(s), t))), decode(t))
{ refl }                               // OutOfFuel, not NotConvertible
```

The meet at `emit(0x800, …)` against `emit(0x80, …)` fails on the spine,
both sides normalize, the `True` branches `emit_scalar(code, rest)` meet
and fail again, and the normalized `is_scalar` chains are then compared to
the bottom. The same at two bytes (`C1` against `C2`) and for a wrong lead
payload. A wrong *tail* or a wrong `emit` minimum is refused as
`NotConvertible` at once: the mismatch is found above the chains. So this
is a rejection-cost problem (controls must fail as a mismatch, not by
exhaustion — `lib_std_bitvec.rs`'s rule), and a positive-cost one for any
theorem whose sides meet only *below* a failed bare meet.

## What to look at

A meet keyed on the run. If `elim_Nat(NatRun p; e)` at a non-accelerable
fold produced a **glued neutral** — head "the run `p` eliminated by `e`",
`unfold` = the one step application it makes today — the δ-lazy stage
would compare two of them as it compares two glued globals: `p = p'`,
`e ≈ e'` (closures over the same body; `leb`'s capture nothing local), and
the spines, before unfolding either. Equal runs settle in the size of `e`
instead of `p`; unequal spines (`code` against `code'`) unfold once to
`match code` against `match code'` and fail at the head. `leb(0x800, …)`
against `leb(0x80, …)` still descends, but only `min(p, p')` levels and
only when the eliminators agree.

Cost: a new neutral head form that every neutral consumer must handle —
`spine_head`, readback and shift, `tm_ne`'s views, typing's neutral
inference, the differential oracle's syntax domain, and DESIGN's
value-representation section — i.e. a change to the value representation,
not a conversion-policy tweak. That is a structural kernel-side design
pass first (the 2026-09-16 verdict on the perf device line: no devices), and it
should be costed against making the *elaborator's* verdict store vouch for
such controls instead. A library workaround exists for nothing here: the
affected statements are rejections.

Repro: `crates/elab/tests/lib_std_utf8.rs`'s prefix plus the snippet
above; `theorem bad(q: BitVec(5), r: BitVec(6), t: List<BitVec(8)>):
decode(Cons(lead2_byte(q), Cons(cont_byte(r), t))) = push_char(decode_seq(C1,
lead2_byte(q), Cons(cont_byte(r), t)), decode(t)) { refl }` is the two-byte
row, also `OutOfFuel` before and after the fix above.
