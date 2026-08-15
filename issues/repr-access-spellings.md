---
title: One designed spelling for a repr's legitimate access points
status: open
labels: [design,frontend,ergonomics]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] item 5, user-confirmed wanted
(2026-08-15). Hand-written certificates today must spell minted names
(`Repr_ListTok::…`, `Impl_ListTok_length::…`, `ListTok_spec_rec`) and
there are TWO spellings for the same access
(`ListTok().mk_Cons(t)` vs `Repr_ListTok::mk_Cons()`), the split forced
by [[theorem-field-projection-oom]] and
[[receiver-method-shadows-record-field]]. The legitimate access points —
the ones user code is *supposed* to reach, as opposed to the internals
[[unnameable-generated-names]] will mark — deserve one designed spelling
(`ListTok::fold`, `ListTok::mk_Cons`, …-shaped), with the workaround
split dissolved rather than papered over: fixing the two underlying
defects is likely the first half of this issue.

## Log

- 2026-08-15: The obligation-records design (docs/obligation-records-design.md §3) hands this issue the REFERENCE spelling deliberately, and hands it a shape to extend. Probed lexer/parser facts it should build on: 'A::b' is a SINGLE lexer token with exactly one join (lexer.rs:130-137), so no three-segment '::' path exists to be spelled; '::' never follows an application (every 'Impl(f, Rp)::refines'-style candidate is a parse error today); '@' is claimed as a PREFIX (fully-explicit call, parser.rs:2492); '.'-chains ('Impl(add, BinNat).refines', 'BinNat.impl(add).refines') parse today and reach name resolution. The design takes '<owner>.<slot>' for the proof-declaration head ONLY, as a KEY resolved in the slot table rather than as an expression — precisely because a dot on an assembled repr/impl value is theorem-field-projection-oom. Consequence for this issue: a dot-shaped REFERENCE form is blocked on fixing that defect first, and until then hand-written proofs keep spelling the minted namespace paths (Impl_Rp_f::refines(), Repr_N::abs()).
