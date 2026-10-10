---
title: Discharge proposition goals in infer by computation and evidence rules
status: open
labels: [elaboration,traits,proofs,ergonomics]
created: 2026-10-10
updated: 2026-10-10
---

`h: P := infer` at a goal that is not a class consults only the derived
table and the locals (`crates/elab/src/resolve.rs` step 1), so
`0 < Succ(k)`, `0 < 5`, `0 < n + 1` and `0 < a * b` all fail even when the
facts that prove them are in scope (probes: `docs/positivity-evidence-design.md` §3).

Round 1 of [[positivity-evidence]]. Add two sources after the locals:

1. **Computation.** A goal that reduces to `True` within a small fuel is
   answered by `trivial`.
2. **Evidence rules.** Registered theorems whose conclusion is a
   proposition, tried by backchaining with each premise resolved by the same
   search (locals first). Keyed so that several rules about one relation
   (`0 < a * b`, `0 < Succ(k)`) coexist, which the class registry's
   (class, carrier head) key refuses.

Also fix the two diagnostic nits the probes found: the failure prints the
parameter's written type (`<(0, n)`) instead of the instantiated goal, and
uses the prefix spelling.

## Acceptance

- Computation discharges `0 < Succ(k)` and `0 < 5`; a goal reducing to
  `False` or stuck is not answered by it.
- A rule `0 < a * b` from `0 < a`, `0 < b` discharges `0 < x * y` from locals,
  and nests (`0 < x * (y * z)`).
- Two rules about `Nat::Lt` coexist; a local still wins over a rule.
- A wrong rule is refused at its declaration or at the kernel gate, never
  accepted silently.
- Negative controls: no rule and no local fails with the instantiated goal
  in the message.

## What it assumes from elsewhere

- **[[implicit-logical-assumptions]]** owns `infer`'s precedence. Assumed
  here: new sources come after locals and derivations.
- **[[traits]]** owns the resolver and its kernel-gated trials.

## Log

- 2026-10-10: Filed from the positivity design; Minus chose rules in `infer`.
