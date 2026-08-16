---
title: Builtin receiver methods claim names before the receiver's type is consulted
status: open
labels: [elaborator,defect]
created: 2026-08-15
updated: 2026-08-16
---

Found in the datarepr v1 round (2026-08-15, docs/datarepr-design.md §1.4 as-landed note 7): `value.fold` on a record value is claimed by the builtin vector receiver method before the receiver's type is consulted, so a record field named `fold` is unreachable by projection. Resolution order should consult the receiver's type first (or at least prefer a field when the receiver is a record). Workaround in the datarepr elaboration: reach through the generated namespace instead of projecting. Related: [[datarepr-separation]], [[theorem-field-projection-oom]].

## Log

- 2026-08-16: Narrowed and re-probed (2026-08-16, the repr-access-spellings round). The datarepr shape this was filed from does NOT reproduce at HEAD: resolve_dot consults the record-field route (lib.rs:4363) before the method desugaring the builtins live behind, so a field wins whenever the receiver's type infers, and every repr access shape infers — ListTok().fold(…), BinNat().fold(…), a hand-written record with fold/head/map fields, off a literal and off a neutral receiver, all check. What still reproduces is narrower than the title: a receiver whose type cannot be INFERRED falls through to the method path and the builtin claims the name, e.g. 'match n { Zero => b(), Succ(k) => b() }.fold(Zero)' at 'record Box { fold: (n: Nat) -> Nat }', which reports `fold` takes `(init, f)` on a vector receiver — a diagnostic that is a lie about a receiver that is not a vector. So the resolution ORDER is not the defect; the fallthrough's diagnostic is, plus the fact that a receiver which failed to infer gets no field-based explanation. Consequence for the repr work: docs/repr-access-spellings-design.md §1 records that neither of the two defects that forced the two-spelling split is load-bearing any more, and §3.2 keeps '.' as ordinary projection without designing around this.
