---
title: split_all fails internally on a match whose scrutinee is a decision built from a Boolean
status: open
labels: [tactics,elaboration]
area: tactics
created: 2026-11-18
updated: 2026-11-18
---

`split_all; all_goals { refl }` on the UTF-8 decoder's last step,
`utf8::emit(min, code, r).holds() = (min.leb(code) && char::is_scalar(code))`,
stops with an internal error: splitting on `Nat::leb(55296, code)` (inside
`char::is_scalar`) builds a motive that is not a type. The match it is stuck
on is `emit_dec`'s, whose scrutinee is `char::is_scalar(code).is_true_dec()`,
a proof of `scalar(code) ∨ ¬scalar(code)` computed from the Boolean; the
Boolean's own tests are what the search reaches.

`examples/utf8/utf8_check.hthr`'s `emit_is_some` keeps its hand proof (a
`match low:` on the bound, then a `match d:` on the decision) because of this.

Expected: split at the Boolean test and carry the decision along (each case
of `is_scalar(code)` reduces `is_true_dec()` to `Inl`/`Inr`), or refuse with
the stuck match named, never an internal error.
