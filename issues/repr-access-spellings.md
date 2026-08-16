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
- 2026-08-15: Shape handed over (2026-08-15) by the obligation-records round: an obligation's printed path is '<owner>::<obligation>' — 'Impl(add, BinNat)::refines', 'BinC::Succ_inv' — chosen on semantic grounds (an obligation is a member of its owner's namespace and '::' is the member operator), ratified by user verdict with the standing instruction that a lexer artifact is a cost to pay and not a vote to count. In v1 it is PRINT-ONLY: it appears in '?' messages, failure diagnostics and 'heather obligations', and nothing parses it, because under inline-first nothing references an obligation from outside the declaration that owes it. So this issue inherits '<owner>::<obligation>' as the shape to extend for REFERENCE position, and two notes with it: the grammar cost is real and unpaid (A::b is one lexer token with one join, and '::' never follows an application, so an applied-owner path needs a new production that modules will force anyway), and the '::' form is the one that does NOT inherit theorem-field-projection-oom, because '.' means value projection and that is the operation that aborts. Citing a certificate inside another proof still spells the minted 'Impl_BinNat_add::refines()'.
- 2026-08-15: UNBLOCKED (2026-08-15): [[theorem-field-projection-oom]] is fixed and closed — projecting a theorem-valued field off an assembled record value now checks (named projections, gendefs.rs), so the dot-shaped REFERENCE form this issue was told to design assuming the fix is free to proceed. Two facts carry over: '.' now genuinely means value projection at law fields (linear, not exponential), and the declaration-time cost of the device is tracked at [[record-projection-defs-declaration-cost]].
