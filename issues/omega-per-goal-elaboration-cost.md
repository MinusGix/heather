---
title: Omega/CutSat: one ordinary linear goal costs tens of seconds to elaborate
status: open
labels: [proofs,elaboration,arithmetic,performance,solver]
created: 2026-09-04
updated: 2026-09-04
---

A single `omega` call on a five-hypothesis linear Int goal is the most
expensive thing in the standard library, and nothing in the cache stack
touches it: it is paid on every edit to the module that contains it and by
every downstream module the moment its prefix is invalidated.

Measured 2026-09-04 (release CLI, cold): `lib/std/omega.hthr` costs ~61 s to
check, all frontend, zero final kernel gate. Per surface item (2026-08-29
attribution, same shape): `cutsat_left_cut` 55 s, `cutsat_right_cut` 32 s,
the two remainder bounds 13 s / 10 s, cancel-middle 6.5 s, remainder-gap
5.6 s -- ten CutSat support theorems are ~136 s of the module's 137 s in
the dev profile. `cutsat_left_cut` is

```
theorem cutsat_left_cut(a, b, x, p, q, remainder: Int,
    scaled_lower: b * (p + remainder) <= b * (a * x),
    scaled_upper: a * (b * x) <= a * (-q),
    commute_product: b * (a * x) = a * (b * x),
    distribute_remainder: b * (p + remainder) = b * p + b * remainder,
    negate_q: a * (-q) = -(a * q)):
    b * p + a * q + b * remainder <= OfNat(0)
{ omega }
```

-- five hypotheses, nonlinear atoms treated opaquely, one conclusion. That
this takes 55 s is a pathology to attribute, not a cost to cache around.

## What this issue owns

Attributing one such goal's elaboration time between (a) Omega/CutSat
search, (b) certificate source generation, (c) elaborating the generated
certificate expression (the `elab_check` of `cert.expr`, which is where
`whnf`/conversion on big generated terms would show), and (d) anything else;
then the deliberate perf round that follows the dominant phase. Reproduce on
`cutsat_left_cut` first, then the affine `seed_680`-style goals in
`crates/elab/tests/omega_cases/mod.rs`.

Not owned here: the scaling rails ([[omega-performance-telemetry]]),
certificate DAG size ([[arithmetic-certificate-dag-sharing]]), or caching
the result across builds ([[persistent-certified-fact-cache]]) -- the cache
makes an unchanged goal free but does nothing for the goal you are editing.

## What it assumes from elsewhere

- **[[omega-performance-telemetry]]** owns the deterministic counts; assumed
  here only that `OmegaReport` can be extended with per-phase timing.
- **[[cutsat-linear-integer-arithmetic]]** owns CutSat's design; this issue
  changes no semantics.
- **[[semantic-module-images]]** recorded the per-item numbers above
  (2026-08-29 log) and is where the equal cold/warm observation came from.
