---
title: omega can't spell an applied function field of a record (nb.number(a))
status: closed
labels: [omega,proofs,ergonomics]
area: tactics
milestone: [none]
created: 2026-11-09
updated: 2026-11-10
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

## Resolution (2026-11-10)

`Speller::applied_field` (crates/elab/src/display.rs) spells a
function-valued field applied as the field read, as `field_read` or a
projection call spells it, then its arguments: `nb.number(a)`, at an inline
projection or a projection definition (a record with parameters). It only
does so when each argument meets an explicit arrow of the field's declared
type, so the spelling re-elaborates to the same spine; an implicit binder or
an aliased function type declines. A source spelling takes only a local
receiver: wider ones reached the kernel at the wrong level
([[applied-field-source-spelling-level-mismatch]]). Diagnostics spell every
receiver, so four refusals the kernel used to report (a spelling gap, not a
skipped check) are now the elaborator's mismatch notes. omega then keys the atom by that
spelling. `field_call_plain` closes, and `Span::offsets_differ`,
`disjoint_offsets`, `offset_has` and `offset_below` are gone, inlined into
`Numbering::spans_distinct`/`spans_apart`/`outside`. Design §21 of
docs/omega-measure-reduction-design.md; probes and the refused
`field_call_apart` are in `lib/_tests/std/tactic/omega_tests.hthr`.
