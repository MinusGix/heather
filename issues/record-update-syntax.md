---
title: Functional record update syntax
status: closed
labels: [surface-syntax,frontend,design]
created: 2026-10-02
updated: 2026-10-03
---

A record has no update syntax. A step that changes one field rebuilds all of
them: `WcState(s.lines, s.words, Succ(s.bytes), True)` in every arm of
`wc_step` (examples/x86-native/wc.hthr). The same holds for tr_s's state, and
for any state machine in the library. A C programmer writes `bytes++`.

Wanted: functional update, sugar for the constructor applied to the old
value's projections, with the named fields replaced. The spelling is open.
Candidates:
- `{ s with bytes = Succ(s.bytes), inside = True }`, which may collide with
  block syntax at `{`;
- `s.with(bytes := …, inside := …)`, which reuses named-argument syntax
  (docs/language/named-arguments-design.md);
- `WcState(..s, bytes := …)`.

Costing (2026-10-02, not built): parser and an elaboration desugar to
`Ctor(e.f1, …)` with `s` let-bound once. The generated term is a constructor
over projections, which the FunctionIR frontend already accepts
(structured.rs reads record fields), so no lowering change. The open question
is a dependent record, where a later field's type mentions a replaced one:
either refuse it or require every dependent field to be given.

Related: [[native-programs-read-like-programs]], [[surface-records]].

## Log

- 2026-10-02: Spelling decided (user, 2026-10-02): s with { f = e }.
- 2026-10-03: 2026-10-03: Landed as `s with { f = v, … }` (docs/language/surface-records.md §6.2): postfix, chaining; elaborated as the record literal with every unwritten field `s.f` (a non-local base let-bound once), in checking and inference. Refuses unknown/duplicate fields, a non-record base, an empty update, and a kept field whose type mentions a replaced one (binder-aware). wc_step's arms now name only what they change. The decided expansion spells a copied input as itself, so a kept Bool field splits with the source's.
