---
title: The in-language analyzers' evaluation cost is the certifying generator's binding constraint
status: open
labels: [performance,elaboration,metaprogramming,compiler]
created: 2026-08-13
updated: 2026-08-13
---

Promoted out of [[certgen-harness-cost]]'s log on 2026-08-13, because it stopped
being a floor and became a blocker: it is the reason
`docs/certgen-ctor-fields-design.md` defers constructor fields.

**What it is.** Running an analyzer is kernel reduction: `analyzer_app` builds
the application, and `certgen.rs`'s `Reader` drives it with
`whnf_term_delta` **spine-directed** — each `whnf` reduces from the top of the
sub-spine it is about to inspect, and nothing is shared between reductions. The
same is true of the certificate fold (`cert_body` applied to the transcriber's
`Ir`). No elaborator spelling round touches any of it: these are not terms the
elaborator emits, they are terms the kernel reduces at analysis time.

**Why it is now binding, with the shape** (numbers in the 2026-08-13 entry of
[[certgen-harness-cost]]): generating one fixture costs ~1x for the shipped
`Nat` fragment, ~18x for the shipped cross-function `mul`, ~24x for a
constructor with ONE bare field, ~100x for one computed field, ~135x for two
bare fields — and a constructor with two fields, one of them computed, does not
finish inside `scripts/test`'s address-space rail at all. Cost tracks the
payload's STRUCTURE, not the body's size. Two hypotheses were tested and
refuted while attributing it: not the marked code's `Pair`/`Inl`/`Inr` type
annotations (replacing them all with `Unit^0` in the marker pass moved nothing
— and the boxed code is never re-checked, so that experiment stays cheap), and
not the walker's own composition (the identical merge, written as a closed
`refl` in `lib/certgen_code.hthr`, reduces for free). What is left is repeated
unshared reduction of `match`es on `Pre` and `TA`, both `Wf`-lowered.

**Levers, in the order the measurement points at them:**

1. **Memoized or normalize-once analyzer evaluation.** One change at the
   invocation seam (`analyzer_app` + `Reader`), with the whole fragment behind
   it; it would also drop `certgen.rs`'s standing in-language-evaluation floor,
   which [[certgen-harness-cost]] records as the residual no verdict cache can
   touch. Watch the CLAUDE.md memory discipline: whatever replaces the
   spine-directed walk must not normalize a whole `Ir` tree at once.
2. **A smaller `TA`.** `lib/certgen_code.hthr`'s accumulator carries `Pre` and
   `Ir`; the `VOut` narrowing already showed what splitting a payload out of it
   buys at elaboration time, and this is the evaluation-time half of the same
   move. Worth measuring after (1), not before.
3. **Re-probe the fields stage.** `docs/certgen-ctor-fields-design.md` §§2–7 is
   designed, implemented and reverted; §9 says what to re-check first.

**Trigger.** Any fragment feature whose fixtures generate slower than the
shipped `mul`, or a second consumer of the analyzer seam.

