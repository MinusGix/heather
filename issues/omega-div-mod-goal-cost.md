---
title: omega closes one-line div/mod goals in seconds: attribute the cost per atom
status: open
labels: [omega,performance,arithmetic]
created: 2026-09-25
updated: 2026-09-25
---

Small `omega` goals over `div`/`mod` by literals cost seconds each. Timings
are from 2026-09-25, release build, `--kernel-workers 1`, cold:

| goal | total | gate | misses | steps |
|---|---|---|---|---|
| `n / 10 / 10 = n / 100` | 0.7 s | 0.3 s | 8,041 | 138K |
| `n / 10 % 10 = n % 100 / 10` | 2.8 s | 0.9 s | 26,441 | 442K |
| `n % 1000 % 100 % 10 / 1 = n % 10` | 3.5 s | 1.4 s | 37,262 | 599K |
| `n % 1000 / 100 = b % 10` from `n = a*10 + n%10`, `a = b*10 + a%10` | 8.2 s | 3.2 s | 83,334 | 1.35M |
| `decimal_line::units_arith` (14 bound/sum goals, record of 26 facts) | 11.3 s | 6.4 s | 139,764 | 2.2M |

(Probe files: `probes/dg/dg.hthr`, `probes/dd/dd.hthr`, and
`lib/decimal_line.hthr`.) The largest `omega` goal above has perhaps six
atoms. The cost looks superlinear in the number of `div`/`mod` atoms, not in
the size of the goal. Each atom brings a quotient variable, a remainder
variable and two bounds, and nested ones compound.

`lib/decimal_line.hthr`'s `omega` lemmas are most of the certified `wc -l`
print build's CPU time. That build now runs within 6% of the test process's
CPU rail under suite load ([[native-print-test-cpu-margin]]).

## Questions

- Where do the seconds go: search, certificate construction, elaboration of
  the certificate (about 60% of the total above is outside the gate), or the
  kernel gate? `OmegaReport`'s phases split the first three.
- Is the `div`/`mod` expansion introducing atoms or constraints that the goal
  never uses? For instance, it could expand `n % 1000 % 100 % 10` fully when
  only its relation to `n % 10` matters.
- Do large literal coefficients cost in the certificate? The `*_arith`
  lemmas carry constants near `2^53` (`1099511627776 * 8000`).
- Would stating each hypothesis to `omega` only when relevant (a
  relevance filter over atoms) cut the certificate? The digit lemmas got
  cheaper when given only the hypotheses they use.

## Acceptance

- The table above as a family in [[omega-performance-telemetry]]'s rails,
  with counts pinned.
- An attribution of the table's top row to a phase, and either a change that
  moves it or a recorded reason the cost is inherent.

## What it assumes from elsewhere

- **[[omega-performance-telemetry]]** owns the rails. This issue is a
  customer family for them.
- **[[omega-cutsat-lemma-cost]]** owns the cost of `omega`'s own library
  lemmas, a different question: this one is about the cost per call site.
- **[[nat-div-mod-lemma-kit]]** takes the digit customers off `omega`
  entirely. This issue remains for the goals that legitimately need it.

## Log

- 2026-09-25: [[nat-div-mod-lemma-kit]] landed. `decimal_line` no longer sends any goal with a `div`/`mod` atom to `omega`, so the table's `units_arith` and digit-lemma rows are gone from the library (the `*_arith` lemmas went from 9–11 s to 15 ms). The table's goals stay this issue's customers as standalone `omega` probes. No library item depends on them now.
- 2026-09-25: The relevance-filter question now has its own owner,
  [[omega-relevant-facts-only]]. Its evidence involves no `div`/`mod`: inline
  `omega` in `times256_value` costs about 375 ms a call, against about 45 ms in
  a small lemma.
- 2026-09-25: [[omega-relevant-facts-only]] landed. `decimal_line::leading_zeros_value`
  went from 3.33 s to 0.17 s, and the `line_*` group items dropped 25–36%.
  The table above predates it and should be re-taken before attributing.
