---
title: Converting a whole-list decoder against a term naming its own per-character decoder exhausts the kernel's fuel
status: open
labels: [kernel, conversion, stdlib]
created: 2026-09-18
updated: 2026-09-18
---

Found writing `lib/std/utf8.hthr` (round 2 of [[string-char-spec-types]]).

`utf8::decode(bytes)` dispatches on a lead byte's class and, in each arm,
returns `push_char(decode_seq(Ck, b, rest), decode(rest'))`. Converting an
application of `decode` at a **three- or four-byte** sequence against a term
that *also* names `decode_seq` (or `decode_char`) at the same bytes aborts the
process with a kernel-worker stack overflow (and reports `OutOfFuel` when the
stack is raised):

```heather
theorem uf3(q: BitVec(4), r, s: BitVec(6), t: List<BitVec(8)>):
        decode(Cons(lead3_byte(q), Cons(cont_byte(r), Cons(cont_byte(s), t))))
        = push_char(decode_seq(C3, lead3_byte(q),
              Cons(cont_byte(r), Cons(cont_byte(s), t))), decode(t))
{ refl }                               // stack overflow
```

The two sides' `decode_seq` arguments are **syntactically identical**, so a
conversion that compared arguments before unfolding would answer in one step.

It is a cliff, not a slope, and the cliff is between payload widths 11 and 16:

| right-hand side | 2-byte (`toNat(11, …)`) | 3-byte (`toNat(16, …)`) | 4-byte (`toNat(21, …)`) |
|---|---|---|---|
| `push_char(decode_seq(Ck, …), …)` | ok | **overflow / OutOfFuel** | **overflow / OutOfFuel** |
| `push_char(emit(min, toNat(n, …), …), …)` — the same thing, one delta-step further reduced | ok | ok | ok |

So one side reducing is cheap and both sides reducing is not. The elaborator's
own conversion accepts `uf3`; only the kernel gate blows up.

## Consequence in the library, already paid

`utf8`'s `push_step` is deliberately stated at the `emit` its class's arm of
`decode` reduces to, rather than at `decode_char`/`decode_seq`, and a
comment there points here. That spelling is the only reason theorems 3–6
close. It is a workaround: the natural statement — "decoding a list is
decoding its head and then its tail" — is the one that is refused.

## What to look at

- Whether `Tc::conv_ty` tries a same-head argument comparison before
  delta-unfolding both sides, and if so why it does not fire here (both
  applications are of the same global to syntactically equal arguments).
- Whether the blowup is in `push_char`'s `match` forcing its scrutinee on both
  sides and then re-forcing per comparison, i.e. missing memoization on a
  shared subterm.
- Reproduction is `crates/elab/tests/lib_std_utf8.rs`'s prefix plus the
  `uf3` snippet above; the 2-byte row is the control that must stay green.

## Log

- 2026-09-18: Re-reproduced 2026-09-18 on the fuel-free `decode` (after [[list-course-of-values-recursion]] landed): the 2-byte control checks, the 3-byte case overflows the kernel stack. The repro above is updated to the current spelling; the fuel was not a factor.
