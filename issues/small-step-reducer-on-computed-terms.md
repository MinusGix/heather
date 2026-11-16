---
title: The elaborator reduces computed records and words with the substitution reducer
status: open
labels: [elaboration,performance,kernel]
area: language
created: 2026-11-16
updated: 2026-11-16
---

The elaborator still reduces computed terms with the kernel's substitution
reducer (`reduce::step_term_delta`) in places where the value machine has
the answer in milliseconds. On 2026-11-16 this was the single largest cost
of the cold library: four declarations hold three quarters of every frame
the reducer stands on, and the largest of them is the heaviest declaration
in the library.

## What the reducer costs

One step of `step_term_delta` finds its redex by walking down every blocked
head and scrutinee above it, and rebuilds each of them on the way out. A
term whose redex sits `d` levels down pays `d` frames, `d` clones and `d`
drops per step, so a reduction of `n` steps costs `n × d`, where the value
machine pays `n`. A loop that runs 64 passes over a record, or a comparison
of two 64-bit words, puts the redex dozens to hundreds of levels down.

Two counters say so exactly, in every `--timings` table since this issue
was filed (`crates/kernel/src/stats.rs`; `scripts/timings --columns
rsteps,rframes`):

- `reduce_steps`: steps the reducer took, whoever asked.
- `reduce_frames`: frames those steps stood on. `frames / steps` is the mean
  depth of the redex.

## Measured

2026-11-16, cloud, test-profile binary, self-checks off, width one, the
whole library in one process (tree f6f6175, elaborator 80ce3d4). The run
took 92 M reducer steps on 1,317 M frames; the evaluator took 1,268 M steps
in the same run.

| declaration | frames | steps | mean depth | seconds: all, `elab_whnf`, `omega_reflect` |
|---|---|---|---|---|
| `Sha256::pad_long` (`sha256_stream_agreement`) | 755 M | 5.2 M | 144 | 61, 60, 0 |
| `clamp_literal` (`simp_branch_tests`) | 177 M | 3.1 M | 56 | 13, 13, 0 |
| `Sched::expand` (`runtime_held_index_tests`) | 56 M | 2.2 M | 26 | 28, 4, 11 |
| `block_spread` (`squash_conditions_tests`) | 30 M | 1.1 M | 29 | 12, 2, 5 |

The rest of the library together is under a quarter of the frames, a few
seconds each at most. (Seconds in a one-process run are inflated against a
build-step worker's; the counts are exact.)

## The callers

**1. `SemanticOracle::whnf_term` when the readback declines**
(`crates/elab/src/oracle.rs`). The value probe finds a canonical head, and
`Readback::term_head` spells its top layer, except for the heads it
declines: an *annotated* pair or injection, and a literal. Declined, the
term goes to `reduce::whnf_term_delta` at the oracle's full fuel.

A record value is an annotated pair. `Sha256::pad_long`'s
`simp_only(Sha256::pad, …)` exposes a goal whose sides are
`Sha256::zero(R, 0).after`, a record a 64-pass zeroing loop computes. A
trace of the declined branch on that one declaration: five reductions of
about eleven seconds each, all `Val::Pair { ann: Some(_) }`, the same term
each time (one per rewrite `simp` fires); every other declined call in the
declaration is microseconds.

`clamp_literal` is the smallest case: `theorem clamp_literal(): clamp(70,
10, 50) = 50 { simp_only(clamp) }`. Two comparisons of `u64` literals, done
by substitution, thirteen seconds, all of it `elab_whnf`. Which head the
readback declined there (the literal or the pair) was not traced.

**2. `omega`'s reduce-and-name** (`crates/elab/src/omega_cert.rs`,
`nat_affine_syntax_within` → `reduce_and_name` → `named_arithmetic_reduct`,
stepping with `SemanticOracle`'s `step_term_delta` at `oracle.rs:496`).
Seventeen of twenty-nine `elab_omega` samples of `Sched::expand` were under
it. The goals are index bounds like `(j + 2).toNat() < 8`. This is the
`omega_reflect_ns` column; it is multiplied by the number of copies of the
body a `decreases` function's companions spell
([[squashed-found-proof-searched-per-copy]]; `block_spread` keeps that
unlifted on purpose).

## Levers

- **Read an annotated pair back.** The readback declines it because the
  value does not say whether the reducer's reduct is the component spelling
  `pair(S; T; a; b)` or the checked one `pair@^T(a; b)`
  (`readback.rs`, `term_head`). Either the value keeps which spelling it
  came from (one bit beside `SigAnn`), or the oracle's contract is relaxed
  from "the reducer's spelling" to "a spelling convertible to it" for the
  callers that only read a shape (`matching::expose` is one). The first
  keeps the debug cross-check (`readback::verify_term`) exact.
- **Literals the same way.** A word or `Nat` literal at the head is declined
  for the same reason (a run stands for both `n` and `Succ(…)`).
- **Never give a declined term full fuel.** A stuck head gets
  `STUCK_SPELLING_STEPS`; a declined canonical one gets `self.fuel`. With
  the value in hand, the reducer is only spelling, and the stuck branch's
  argument (past the budget, the input is the answer) holds here too
  wherever the caller can take an unreduced term.
- **Memoize `expose` per `simp` run.** The five reductions of `pad_long`
  are one term.
- **`reduce_and_name` on values.** It walks reducts one step at a time to
  find the first one whose head is arithmetic `omega` knows. The value
  machine's neutral spine names the same thing without rewriting the term.
- **The reducer itself.** A step that returned its context (a zipper)
  would resume where the last one stopped and lose the factor of `d`. It is
  the kernel's reference semantics, so this is the last lever, not the first.

## Benches

`scripts/bench-probes --filter reduce/` and `--filter omega/`
(`perf/bench/cases.tsv`): `reduce/pad-long`, `reduce/clamp-literal`,
`omega/sched-expand`, `omega/block-spread`. `reduce_steps` and
`reduce_frames` are among the counters a row records, so a fix shows as
those two falling, exactly.

Acceptance: `clamp_literal` and `pad_long` elaborate with `reduce_frames`
within a small multiple of their `reduce_steps`, and neither is among the
library's hundred heaviest declarations.

Related: [[elab-whnf-copies-straight-continuations]] (the type-side
readback this extends), [[elaborator-whnf-probes-on-computing-types]]
(closed: the probe/spell split), [[whnf-sharing-term-growth]].

## Log

- 2026-11-16: **Two callers fixed; the reducer and the readback are as they were.** Traced first: every slow reduction in `pad_long` and `clamp_literal` ended in `OutOfFuel`. The reducer spent its whole fuel (2^20 steps, seconds) on a head the value machine had, and the caller, motive exposure, carried on without the answer. A word comparison is one step for the machine and a walk over 64 bits for the reducer, so those heads were never within its reach.

  - `SemanticOracle::whnf_term_probing` (`oracle.rs`): `whnf_term` for a caller that carries on without an answer. The value probe keeps the oracle's fuel; the reducer's spelling of a declined canonical head is bounded by `DECLINED_SPELLING_STEPS`. `Elaborator::read_motive_term` (so `matching::expose`) uses it. `whnf_tm` and every caller that decides something keep the full fuel: `absurd(cong_fn(λ word => word.toNat(), same))` in `stream_filter_spec` needs a spelling 50,000 steps away and gets it. (Bounding `whnf_term` itself was tried first and broke exactly that proof.)
  - `reduce_and_name` (`omega_cert.rs`) leaves `BitVec::toNat` of a word that is not a constructor value alone. Its gate ("an argument is a constructor value or a numeral") let every word value through on the width. Traced on `block_spread`: 2,431 calls on five distinct terms, each walking 511 reducer steps over a stuck fold and naming nothing.

  Bench cases, before → after (master 31de154, where `bv_omega` changes merged since the baselines had made `omega/block-spread` 1.9 times slower on their own):

  | case | seconds | reducer frames |
  |---|---|---|
  | `reduce/pad-long` | 59.5 → 1.1 | 755 M → 0.23 M |
  | `reduce/clamp-literal` | 13.0 → 0.02 | 177 M → 0.11 M |
  | `omega/block-spread` | 18.4 → 9.6 | 45.6 M → 0.49 M |
  | `omega/sched-expand` | 24.3 → 21.9 | 58.5 M → 1.3 M |

  What is left, and why this stays open: the readback still declines an annotated pair and a literal, so a caller that needs the spelling (`absurd`, `whnf_tm` at large) still pays the reducer, and one whose head is past the fuel still fails after seconds. The exact fix is the first lever above: the value has to say which spelling it came from (`Term::Pair`, `Term::PairAt` with its un-reduced annotation, or a vector's unfolding), which is a field in the kernel's `SigAnn`. `Sched::expand` barely moved in seconds although its reducer work fell forty-fold: its cost is now omega's own search and the evaluator, not this reducer.
