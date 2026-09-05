---
title: Omega/CutSat: one ordinary linear goal costs tens of seconds to elaborate
status: closed
labels: [proofs,elaboration,arithmetic,performance,solver]
created: 2026-09-04
updated: 2026-09-05
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

## Log

- 2026-09-05: ATTRIBUTED AND FIXED (2026-09-05, release CLI, library prefix replayed from images). Per-goal phases on cutsat_left_cut: reflect+search+render+parse together <10 ms; checking the generated 33 KB certificate 32.1 s -- i.e. (c) alone. Perf (frame pointers): 91% under Elaborator::whnf, split 74% at the checking fallback's universe probe (lib.rs '_' arm: whnf(expected) to see whether a Ty hides under El) and 26% at ctor_here_expected's whnf, reached for *qualified lemma names* (omega::normalized_le_upper etc.) because only_ctors_visible is vacuously true when a name has no unqualified entries. Each probe ran reduce::whnf_type_delta on El^0(Le(x, dot(row, atoms))) -- unfolding Le at Int to a match, hence computing the dot product by substitution -- and single reductions cost 1-7 s (26 probes = 25.8 s of the 32 s). FIX (two guards, no semantics): the universe probe skips an El at level 0 (El^{1+l}(Ty l) is the only rule producing a Ty), and ctor_here_expected stands down on a qualified name whose qualifier no module declares as an inductive (Names::declares_any_as, scope-free so Option::None still resolves through the expected type). AFTER: left_cut check 32.1 s -> 0.25 s; the ten omega calls in lib/std/omega.hthr 65 s -> 1.09 s; the omega closure (cold, release) ~95 s -> 16 s. INSTRUMENTATION KEPT: OmegaReport.phases (OmegaPhases: depth, source_len, reflect/omega_search/cutsat_search/render/parse/reconstruct/check ns; check inclusive of nested omega uses, depth says which) and the CLI prints one line per invocation of a freshly checked module under HEATHER_OMEGA_PHASES=1 (crates/cli/src/semantic.rs). The mechanism that remains -- whnf probes are the small-step reducer, pathological on any computing proposition -- is filed as [[elaborator-whnf-probes-on-computing-types]] with its levers.
- 2026-09-05: Full suite caught one consumer that relied on the fallback's reduced hint: cong's LGG trigger (solve_from_expected) unified against the expected type as handed over, so a RelId<Nat>(a, b) goal -- an El^0 that only δ-unfolds to a = b -- stopped inferring cong's f (lib_setoid_mergeable::contextual_rewrite_specializes_to_identity_and_enforces_its_bound). solve_from_expected now reduces the expected type itself, once, for both its halves (it already did for the harvest half). Reproducer unchanged at 0.26 s: omega's lemmas carry no implicits, so this path is not on the certificate.
- 2026-09-05: Final full suite (2026-09-05): 2347 passed, 0 failed, one target INCOMPLETE -- function_ir_x86_alu SIGKILLed at the 300 s CPU rail under 7-way contention, the pre-existing rail-hugging [[parallel-test-memory-headroom-under-heavy-prefixes]] records. Serial control on the same machine: that target takes 268 s at the base commit and 117 s on this branch, so the probe guards are a 2.3x win there too (x86 lowering checks arguments at computing propositions as well), not a cost. Closing condition met for this issue's own scope: attribution done, dominant phase fixed, instrumentation kept; the residual mechanism has its owner.
