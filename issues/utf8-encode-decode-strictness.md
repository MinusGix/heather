---
title: Prove the UTF-8 strictness theorem: a decoded value re-encodes to its bytes
status: open
labels: [stdlib,proofs,utf8]
created: 2026-09-18
updated: 2026-09-18
---

Round 2 of [[string-char-spec-types]] closed `decode(encode(s)) = Some(s)`,
`encode_injective`, `encode_append` and `toString_ofString`
(`lib/std/utf8.hthr`) but not the converse,

```heather
theorem encode_decode(bytes: List<BitVec(8)>, s: String, p: decode(bytes) = Some(s)):
    encode(s) = bytes
```

which is what makes `Utf8 ≅ String` (with it, `ofString(u.toString()) = u`
through a `bytes_injective` for `Utf8`). The decoder was not weakened to
get it; the stop rule in `docs/string-char-design.md` §5.4 was taken.

Where it stalls (design §5.5): the hypothesis is at an abstract byte list,
so the proof must case on `class_of(b)`, but `decode` computes the class
inside its body and there is no subterm to abstract with `match … as`.
Naming the per-class body makes it mutually recursive with the loop, and
[[mutual-recursion-measure-synthesis]]'s `decreases` requirement loses the
unfolding equation again.

Route: hoist the four tail results out of the class dispatch so the
per-class body takes them as `Option<String>` arguments and stops being
recursive; then the remaining work is ordinary — `bitvec::ofNat_toNat` and
`bitvec::toNat_lt_pow` (neither exists), five "rebuild the byte from
payload + class bits" lemmas, the converse of `width_bounds`, and inversion
lemmas for `push_char` and `emit`.

The first step is **smaller since 2026-09-18**: [[list-course-of-values-recursion]]
landed and `decode` recurses on `rest`/`rest2`/`rest3`/`rest4` directly, so
the fuel and the `decode_at`/`decode` pair are gone. The loop's arms now read
`push_char(decode_seq(Cᵢ, b, rest), decode(restᵢ))` — the tail results are
already one syntactic subterm each — so the hoist is a re-spelling of one
`fn` rather than an untangling of fuel arithmetic. The obstacle itself is
unchanged: `class_of(b)` is still computed inside the body.
