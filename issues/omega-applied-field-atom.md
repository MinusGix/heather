---
title: omega can't spell an applied function field of a record (nb.number(a))
status: open
labels: [omega,proofs,ergonomics]
area: tactics
milestone: [none]
created: 2026-11-09
updated: 2026-11-09
---

`omega` fails with "Omega could not spell a natural expression" when a
fact or goal has a **function-valued record field applied to an argument**
as an atom, record parameter or not:

```text
record NumC { number: Nat → Nat }
theorem field_call_plain(nb: NumC, a, k, top: Nat, h: nb.number(a) + k <= top): nb.number(a) <= top { omega(h) }
  -- Omega could not spell a natural expression
```

Found building `Numbering` in `lib/std/machine/memory.hthr`
([[address-interval-sets]]): every `omega` over `nb.number(a)` had to move
into a Nat-only helper taking the applied field as an argument
(`Span::offsets_differ`, `Span::disjoint_offsets`, `Span::offset_below`,
`Span::offset_has` in `lib/std/data/set/span_set.hthr`), and an unrelated
fact in scope breaks an `omega` that would otherwise close. Same family as
the closed [[omega-record-projection-atoms]] (a plain field of a local), whose
fix covered the projection but not its application.

Shape of a fix: spell `r.f(args)` as the field read applied, as the
display speller does for a field read; key the atom by it.

## Done when

`field_call_plain` above closes by `omega`, and the four helpers are
inlined back into `Numbering::spans_distinct`/`spans_apart`/`outside`.
