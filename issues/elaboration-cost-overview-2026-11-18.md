---
title: Where cold elaboration of the library goes on 2026-11-18
status: open
labels: [performance,overview,elab,kernel]
area: infrastructure
created: 2026-11-18
updated: 2026-11-18
---

A cold check of the whole library, one process, attributed by `--timings`, taken because the core language should not be this slow before any image reuse (Minus, 2026-11-18). The aim is not a faster number on this run but benchmarks that poke at the costs it shows, so a slope says which part to optimize (`perf/bench/`, `scripts/bench-frontend`). It follows [[performance-overview-2026-11-11]] and [[small-step-reducer-on-computed-terms]].

## How it was measured

One 4-vCPU cloud container (`docs/infrastructure/cloud-benchmarks.md`), master fa7116c (#778), the test-profile `heather` the suite runs (hot crates at opt-level 3), kernel width one, nothing else running:

    HEATHER_KERNEL_WORKERS=1 heather check --cache --cache-dir <empty> --expectations --timings all.tsv lib

The TSV is not committed (10 MB); rerun the command to get it back. The run takes about 28 minutes.

## The totals

- **1,667 CPU-s** for 658 modules, 38,028 item rows and 50,787 kernel-checked declarations.
- A release binary was 8% faster than the test-profile one on `lib/std/analysis` cold (177 against 192 s), and `--timings` cost about 2%, so neither is a lever. (The 24% `--timings` overhead of the 2026-11-11 notes no longer holds.)
- At four cores with perfect packing that is still over 400 s of wall time cold. Reuse is what turns a cold check into a warm one, but the language's own cost is what this issue is about.

## By phase (CPU-s, item and module rows)

| phase | s | share |
|---|---|---|
| kernel gate | 603 | 36% |
| declaration bodies | 289 | 17% |
| unattributed (`other`) | 289 | 17% (249 inside items; most in `runtime fn` generator modules) |
| resolve (instances) | 68 | |
| elaborator whnf | 65 | |
| omega (reflect 36, check 28, reconstruct 20, parse 6, rest) | ~96 | |
| merkle walk | 47 | |
| image relocate (building each module's world, ~0.1 s × 451) | 45 | |
| unify | 40 | |
| declaration types | 30 | |
| instance match | 27 | |
| image publish | 20 | |
| matching | 19 | |

## By area

- `lib/native`, `lib/lang` and `lib/_tests/native`: **848 s**, about half. Gate 360 s, unattributed 223 s.
- `lib/std`: 409 s. `lib/_tests/std`: 261 s.
- The top 50 modules are 60% of the run. Heaviest: `native_compile_correct` 71, `function_ir_learn` 47, `supremum` 43, `runtime_held_index_tests` 41, `lexer_scan` 38, `x86_64` 29, `runtime_lifted_loops_tests` 28, `function_ir_lower_calls` 27, `closed_interval_tests` 25, `eft` 24.
- Unattributed time by module: `lexer_scan` 18 of 38, `runtime_held_index_tests` 12 of 41, `sha256_compression` 11 of 23, `sha256_stream` 11 of 20, `runtime_held_call_tests` 10 of 20, `runtime_held_tests` 9 of 18, `lexer_records` 9 of 23. Every one is a `runtime fn` module.

## By declaration size

| band | items | s |
|---|---|---|
| ≥ 10 s | 7 | 167 |
| 1 to 10 s | 261 | 665 |
| 0.1 to 1 s | 1,664 | 457 |
| < 0.1 s | 36,096 | 229 |

So about 270 declarations are half the cost, and 36,000 small ones are an eighth.

- In the 1 to 10 s band the gate dominates 146 items (358 s), unattributed time 62 (158 s), bodies 32 (79 s). Phase sums: gate 287, other 157, bodies 96, elaborator whnf 28.
- In the 0.1 to 1 s band the gate dominates 836 items (230 s), bodies 457 (109 s), unattributed time 199 (66 s).

## The heaviest declarations

| s | module | item | where | counters |
|---|---|---|---|---|
| 51.3 | native_compile_correct | `Target::procedures_body` | gate 31.0, body 4.2, resolve 3.9 | 432 M subst nodes, 119 M syntax-eq, 833 k conv misses, 1.5 GB peak |
| 33.2 | supremum | `OrderComplete::below_located` | resolve 19.7, body 8.2, gate 4.7 | 250 M subst nodes |
| 25.9 | runtime_held_index_tests | `Sched::expand` | elab whnf 7.1, omega reflect 4.8, other 4.3 | 26 M steps, 803 k reducer steps, 45 k unify calls |
| 22.0 | closed_interval_tests | `cubic_nonconst` | body 10.9, resolve 5.5, gate 4.6 | 161 M subst nodes |
| 13.4 | x86_64 | `decode_opcode_reference` | body 4.7, matching 4.4, gate 2.3 | 246 M syntax-eq nodes, 2.2 M reducer steps |
| 10.7 | sha256_compression | `Sha256::rounds` | other 5.1, gate 4.8 | 13 M steps |
| 10.4 | linux_x86_64_stack_growth | `stack_touches_run` | omega reflect 4.2, gate 3.0, reconstruct 2.5 | 104 M subst nodes |
| 9.9 | squash_conditions_tests | `block_spread` | elab whnf 4.1 | 384 k reducer steps |
| 9.5 | sha256_schedule | `Sha256::expand` | gate 4.3, other 3.7 | 14 M steps |
| 9.4 | function_ir_refusal | `File::call_refusal` | gate 7.1 | 696 k conv misses |
| 8.2 | itree_trace | `IsTrace::split_bind` | gate 6.7 | 56 M subst nodes, 693 MB peak |
| 7.1 | function_ir_learn | `Seen::beside` | gate 2.8, body 2.7 | 7.4 M reducer steps |
| 6.6 | function_ir_learn | `Seen::ordered` | body 4.0 | 9.7 M reducer steps, 44 M syntax-eq |

`below_located` was 11 s on 2026-11-11 ([[instance-resolution-on-the-reals]]); its resolution alone is now 20 s.

## Counters over the run

1.6 G evaluator steps, 2.9 G local-substitution nodes, 2.0 G syntax-equality nodes, 368 M global-shift nodes, 246 M reducer frames, 12 M conversion misses, 6.2 M declarations gated.

## Findings

Each heavy declaration was rerun alone (`--only`, test-profile binary, kernel width one), sampled with gdb, and where a cause showed, counted with temporary instrumentation. A time from an `--only` run is the declaration's own; its counts reproduce a whole run's.

1. **A `for` over words is exponential in its body's statements**: [[word-loop-body-exponential]]. Four assignments to a `u64` field cost 0.7 s, eight 38 s, sixteen hit the 600 s rail. Bench family `loops/word-body`, slope 3.5. Fixed 2026-11-18: the cause was the loop's companions spelling a `let`'s value once per read (the probes only multiplied it); slope 0.75 now.
2. **Plain-match arms rebuild both types at every checking fallback**: [[match-arm-coercion-abstracts-both-types]]. That is 18.4 of `below_located`'s 27.7 s (260 checks, all misses) and 4.8 of `cubic_nonconst`'s 16.8 s. Bench families `match/arm-checks`, `match/plain-checks` and `match/arm-type-size`; probe cases `analysis/below-located` and `analysis/cubic-nonconst`.
3. **The type-code template instance table compares arguments deeply**: [[template-instance-table-deep-compare]]. 231 M of `decode_opcode_reference`'s 252 M syntax-equality nodes. Probe case `x86/decode-opcode-reference`.
4. **The `runtime fn` modules' unattributed time is the generator**: running on the kernel's evaluator through the host, and its reply read one field at a time with a fresh evaluator per read. Logged on [[runtime-generator-link-cost]]; probe case `runtime/sha256-rounds`.
5. **`Target::procedures_body`** is still [[small-step-reducer-on-computed-terms]]'s substitution over one long proof: 231 M local-substitution nodes in elaboration alone. **`Sched::expand`** is the reducer under omega's reflection, as that issue says. Neither has a new cause.
6. **The gate, across items**: a least-squares fit of gate time against the counters over the 1,456 items with a gate above 50 ms (R² 0.88) puts it at about 160 ns per evaluator step, 11 µs per conversion miss and 29 ns per local-substitution node. Most of the gate is the evaluator and conversion at those rates, not one pathology. The outliers per step are worth their own look. Over the 537 gate-dominated items between 0.1 and 10 s, the median is 518 ns per step, the 90th percentile 2.8 µs and the 99th 13 µs; 77 items above three times the median hold 44 s. `float/exp-one-64` (6.7 µs a step, almost no substitution or conversion: large rationals) is the probe case.

## The middle bands, sampled

A random sample, stratified by dominant phase, of the 1 to 10 s and 0.1 to 1 s bands, with four of them profiled alone:

- `closed_interval::UnifContOn::ivt_steps` (4.3 s, 26 M substitution nodes in the body): `linarith` inside a match arm. Its time is in `ring.rs`'s `local_edge_law`, which spells each candidate morphism law as source, parses it and elaborates it to see which one fits an image. `below_located` passes through the same code. Not measured on its own yet. It is the next thing to count.
- `eft::Format::two_sum_pos` (gate 4.8 s, 1.7 M steps, 25 M substitution nodes): the gate's typing walk. Nothing beyond finding 6.
- `sha256_stream_agreement::Sha256::close_short` (2.4 s, body): `simp`'s unfolding walk (`goal_combinators::simplify_goal_unfolding`, `contracted`) and `terms_convert`.
- `eft::Finite::vk_unflip` (0.26 s): nothing stands out. The 0.1 to 1 s band is 836 gate-dominated items and 457 body-dominated ones with no common cause in the sample, which is what a cost spread across shared mechanisms looks like (finding 6).

## Log

- 2026-11-18: measured and filed; the heaviest declarations and a sample of the bands profiled, four issues filed or logged, the bench families and probe cases above added.
