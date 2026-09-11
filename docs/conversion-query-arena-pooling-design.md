# Pooling the conversion query's body cache and value arena — design

Deliberate perf round on `issues/conversion-query-arena-pooling.md`, 2026-09-11.
The issue names two levers. This design **takes the first and refuses the
second**, because the measurement that was supposed to size the second sized it
at zero or worse.

Every mechanism below was hand-run on one furnace box
(`furnace-bb0218be4a`, AMD EPYC 9J14, 16 cores) before it was written. The
throwaway instrumentation is this round's scratch `probe-full.diff` — an env-switchable
arena policy (`HEATHER_PROBE_ARENA`), an env-switchable shared body cache
(`HEATHER_PROBE_BODIES`), and a nodes-per-query histogram folded into
`ValueMetrics::conv_miss_report`. It is not in the tree; it is the prototype the
implementing pass should read before writing the real thing.

## 1. Attribution: where the 30% actually is

`scripts/measure-x86-conv-miss` (five-node FunctionIR/x86 module, dev profile,
`value-metrics`) with the histogram probe on:

```
probe queries=11671 nodes=6729349 envs=1620830 levels=63116 elims=17011
                                  terms=2312408 types=2715984
```

| nodes in the query's five arenas | queries | share | cum. | share of all nodes |
|---|---|---|---|---|
| < 32 | 3 864 | 33.1% | 33.1% | 1.6% |
| 32–63 | 5 124 | 43.9% | 77.0% | 2.9% |
| 64–255 | 1 917 | 16.4% | 93.4% | 4.0% |
| 256–1 023 | 430 | 3.7% | 97.1% | 2.8% |
| 1 024–16 383 | 93 | 0.8% | 97.9% | 5.8% |
| **16 384–32 767** | **242** | **2.1%** | 100.0% | **81.9%** |
| 32 768–131 071 | 1 | 0.0% | 100.0% | 1.1% |

The distribution is **bimodal, and neither mode is what the issue assumed.**
Three quarters of queries are under 64 nodes, and 243 queries hold 83% of the
node production. "Tens of thousands of queries against one Ψ" is also off by an
order of magnitude at this size: 11 671 queries for the *whole* module, the
largest single gate being `mixed_binary_alu_x86_gprs_congruent` at 1 678.

Now cost the five components the round was chartered to separate.

**(a) typed_arena chunk growth.** `Arena::new()` in typed-arena 2.0.2 is
`with_capacity(INITIAL_SIZE / size_of::<T>())` with `INITIAL_SIZE = 1024` — an
**eager ~1 KiB `Vec` per arena, allocated before the query touches it**, five
per `ValueArena`. So the module pays 11 671 × 5 ≈ 58 000 chunk
allocate/free pairs of about a kilobyte each, plus the doubling ladder of the
243 large queries (roughly ten chunks each, ~2 400 more).

**(b)+(d) per-node allocation inside a query.** The same run reports
`type_cache_inserts: 1894881`, `term_cache_inserts: 49249`, `evictions: 0`,
`type_cache_peak: 6911`. Every insert is an `Rc<VTy<'v>>` / `Rc<Val<'v>>`
allocated on the heap and freed when the query ends; the arena nodes themselves
(6.7 M of them) are bump allocations that cost the allocator nothing.
**1 944 130 heap allocations against ~60 000 from (a): a ratio of 33 : 1.**

**(c) `Env::new` fixed setup.** `Rc::new(psi.clone())` and
`Rc::new(BodyCache::new())` are two more small allocations per query — 23 000
for the module, in the same order as (a) and two orders below (b).

**(e) body rebuilds.** The cache is per query, so each of the 11 671 queries
re-runs `shift_global(v+1)` for every definition it unfolds for the first time.
This is the `map_type`/`map_term<ShiftGlobal>` ~8% of the 2026-09-06 profile,
and it is the one line item that has nothing to do with the allocator.

**The conclusion the numbers force:** the allocator share is the value caches'
`Rc` traffic — category (d), "per-node allocations inside a query that no
pooling reaches". Arena pooling addresses about 3% of the allocation *count*.
§2 measures that directly rather than arguing it.

## 2. Lever 2 is refused, by its own measurement

Three arena policies were built into one binary and selected by env var:

- **mode 0** — `Arena::with_capacity(0)` for all five: no eager chunk at all.
- **mode 1** — stock `Arena::new()`.
- **mode 2** — `Arena::with_capacity(high-water mark of that arena kind so
  far)`: the brief's option (i), which removes the growth ladder *entirely*
  without reusing any live storage, and is therefore the strict upper bound on
  what pooling-without-a-custom-allocator can win.

Five-node module, `mixed ALU kernel=` seconds, three repetitions, same job:

| policy | kernel s | vs stock |
|---|---|---|
| stock (mode 1) | 0.998 / 0.996 / 0.992 | — |
| mode 0 | 1.005 / 0.998 / 1.007 | +0.9% |
| mode 2 | 1.095 / 1.089 / 1.008 | +4.9% |

Cold `heather check lib/std/omega.hthr`, release CLI, wall seconds:

| policy | wall s | vs stock |
|---|---|---|
| stock | 9.98 / 10.21 / 10.21 | — |
| mode 0 | 10.42 / 10.35 (earlier job, same box) | +1.5% |
| mode 2 | 10.13 / 10.26 / 10.20 | +0.5% |

Both alternatives are **at best neutral and usually worse**, and the histogram
says why mode 2 in particular is a trap: the high-water mark is ~32 000 nodes,
so sizing every query from it makes a twelve-node query reserve about a mebibyte
across five arenas. Sizing per query from a global maximum is exactly wrong for
a bimodal distribution.

Option (ii), a first-party bump region with a reset, would remove the same
~3% of allocations that mode 0 and mode 2 already remove for free, at the cost
of hand-written allocation inside a kernel whose discipline section says
"correctness over performance throughout". **The verdict is option (iii):
change nothing about the arena.**

What this leaves behind, and where it should be filed rather than assumed: the
real target is that `ValueArena::cache_ty` / `cache_tm` memoize into
`Rc<VTy<'v>>` / `Rc<Val<'v>>`, one heap allocation per forced node. The same
medicine already applied to elimination spines and environment cells
(`issues/value-domain-allocation-constant.md`, 2026-09-02) — put the memoized
value in the query arena and key the cache by `&'v` reference — is the change
that reaches the 1.94 M allocations. It is a representation change across
`eval.rs`'s force paths and the `Dom` API, not a cache-lifetime change, so it is
a separate round with its own falsifier, not a slice of this one.

## 3. Lever 1: one `BodyCache` per gate

`Defs::body(v)` is `bindings[len - 1 - v].body.shift_global(v.0 + 1)` — a pure
function of (Ψ, index). `conv::Env` already states the rule: the cache belongs
to one Ψ, and the one operation that changes Ψ (`push_tele`) rebuilds it. The
defect is only that the owner is a *query* rather than the gate, so the memo is
thrown away 11 671 times over one module and the term rewriter's
`Tc::whnf` never had one at all.

### The shape

`crates/kernel/src/typing.rs`

- `struct Env` gains `bodies: Rc<BodyCache>`.
- Each `Env { … }` literal builds `Rc::new(BodyCache::new())`: the per-binding
  env in `check_global_bindings` (~line 170), the eight public entry points
  (~lines 223–368), and the test helper (~line 2436).
- `in_ctx` and `push_entry` inherit it through `..self.clone()`. Both keep Ψ
  fixed, so every key still denotes the same binding.
- `push_tele` **must** install a fresh cache — it is the only operation that
  changes Ψ. Mirror `conv::Env::push_tele`'s comment; a shared cache here would
  be a soundness bug, not a slowdown.
- `Tc::whnf` (~line 731) switches `Defs::transparent(&env.psi)` to
  `Defs::transparent_cached(&env.psi, &env.bodies)`. This is the bodies-less
  rewriter path the brief asked about, and it is the `SubstGlobal` ~4%.
- `Tc::conv_ty` (~line 700 and the `value-metrics` variant at ~670) and the
  `TyLam` `conv_local_ctx` site (~line 1104 / ~1116) pass
  `Rc::clone(&env.bodies)`.

`crates/kernel/src/conv.rs`

- `Env::new_with(arena, psi, gamma, layer, bodies: Option<Rc<BodyCache>>)`, with
  `Env::new` delegating with `None`. Every existing caller is unchanged.
- Four `pub(crate)` entries that typing uses: `conv_type_cached`,
  `conv_type_cached_with_metrics`, `conv_local_ctx_cached`,
  `conv_local_ctx_cached_with_metrics`.

**The public signatures do not move.** `conv_type`, `conv_term` and
`conv_local_ctx` keep their current arity, which is what keeps the elaborator
(`oracle.rs`, `forded.rs`, `indexed.rs`, `vec.rs`) and roughly forty test files
out of this change. `BodyCache` is already `pub` and `elab/src/certgen.rs`
already owns one, so no new surface is exported.

`reduce.rs` does not change.

### Why the gate is the ceiling

A `GlobalVar` is counted from the inside: `i = psi.bindings.len() - 1 - v.0`.
The elaborator pushes a binding per declaration, so at the next gate every index
denotes a different binding and no entry survives. A cross-gate cache would have
to be re-keyed, which is a different design. Per-gate is not a compromise; it is
the largest sound scope.

### What it measures

Five-node module, `mixed ALU` seconds, three repetitions:

| | kernel s | total s | peak RSS |
|---|---|---|---|
| before | 0.998 / 0.996 / 0.992 | 1.708 / 1.715 / 1.707 | 541.1 MB |
| lever 1 | 0.869 / 0.870 / 0.871 | 1.585 / 1.582 / 1.592 | 541.8 MB |
| | **−12.6% kernel** | −7.2% total | +0.1% (noise) |

Cold `heather check lib/std/omega.hthr`, release CLI, three repetitions:

| | wall s | peak RSS |
|---|---|---|
| before | 9.98 / 10.21 / 10.21 | 192.7 MB |
| lever 1 | 9.86 / 9.59 / 9.89 | 190.0 MB |
| | **−3.4% median** | **−1.4%** |

Peak RSS does not rise on either workload, and on Omega it falls: the per-query
rebuild was itself transient allocation. The retained set is bounded by one
`Rc<Term>` per definition *actually unfolded during the gate*, at most |Ψ|.

Lever 1 combined with arena mode 2 measures 0.901 / 0.970 / 0.933 — worse than
lever 1 alone, which is one more reading of §2. **Do not land them together.**

## 4. The before column

Everything below was recorded in one job on `furnace-bb0218be4a` at tree
`9ae0855` plus the probe diff, and is the reference *shape*; the implementing
pass must retake its own before column on its own box in its own job, because
box-to-box variance is ~35%.

| row | before |
|---|---|
| five-node module, `mixed ALU kernel=` (dev, TIMINGS only) | 0.998 / 0.996 / 0.992 s |
| five-node module, `mixed ALU total=` | 1.708 / 1.715 / 1.707 s |
| five-node module, peak RSS | 541.1 MB |
| Omega closure, cold release `heather check`, wall | 9.98 / 10.21 / 10.21 s |
| Omega closure, peak RSS | 192.7 MB |
| module queries / arena nodes | 11 671 / 6 729 349 |
| `type_cache_inserts` / `term_cache_inserts` | 1 894 881 / 49 249 |

`scripts/bench`, recorded fresh on the same box (`--save`, then `--check`
reporting `ok: 106 comparisons within thresholds`):

| family | cases (time, median) | slope |
|---|---|---|
| `subst/shift-closed` | 64:143 ns, 128:143, 256:147, 512:147, 1024:143 | 0.01 |
| `nat/add-normalize` | 64:12.87 µs, 128:25.53, 256:51.05, 512:102.18, 1024:204.30 | 1.00 |
| `nat/mul-normalize` | 8:12.31 µs, 12:26.66, 16:46.47, 24:102.58, 32:180.48, 48:401.47 | 1.95 |
| `nat/check-numeral` | 64:1.85 µs, 128:3.92, 256:8.25, 512:18.26 | 1.10 |
| `conv/computed-numeral` | 32:25.33 µs, 64:49.07, 128:96.17, 256:193.40, 512:388.89 | 0.99 |
| `conv/perturbed-pairs` | 25:64.69 µs, 50:136.43, 100:289.35, 200:593.34 | 1.07 |
| `conv/simulate-payload` | 32:60.70 µs, 64:60.42, 128:60.56, 256:60.43, 512:60.35, 1024:60.33 | −0.00 |
| `conv/simulate-depth` | 16:15.17 µs, 32:29.95, 64:59.72, 128:120.70, 256:246.82 | 1.01 |
| `wf/check-tree` | 303:54.34 µs, 683:120.24, 1443:251.75, 2963:509.61 | 0.98 |
| `wf/mirror-involution` | 303:120.83 µs, 683:280.36, 1443:606.17, 2963:1.20 ms | 1.01 |
| `code/check-identity-recursor` | 3:300.94 µs, 5:337.43, 9:345.55, 17:353.28, 33:354.00 | 0.06 |
| `code/whnf-identity-recursor` | 3:503 ns, 5:526, 9:520, 17:519, 33:523 | 0.01 |
| `check/generated-terms` | 25:591.02 µs, 50:648.32, 100:1.78 ms, 200:4.85 ms | 1.06 |
| `stack/check-numeral` | 1521 levels, 2.7 KiB/level | — |

## 5. The bar, and two things about it that are not true as chartered

The bar for the implementing pass:

1. Five-node module `mixed ALU kernel=` at or below the before median on the
   same box. Expect ≈ 0.870 s against 0.996 s.
2. Cold Omega `heather check` wall at or below the before median. Expect
   ≈ 9.86 s against 10.21 s.
3. Peak RSS not above before on either. Expect flat and flat-to-down.
4. `scripts/bench`: the constant families move together, no exponent change.
5. Every row of §4 re-taken, so a rise somewhere unchartered is visible.

**Refutation 1 — `scripts/bench --check` cannot gate time on a furnace box.**
`crates/kernel/benches/baseline.tsv` was recorded on an AMD Ryzen 7 5700X; the
furnace is an EPYC 9J14, and the harness detects the mismatch, degrades to
"shape-only: 18 comparisons within thresholds — 88 skipped for a baseline env
mismatch", and **exits 3**, which `scripts/bench` reports as a failure. The
working protocol, verified in this round's job 3:

```
scripts/bench --save      # at the BEFORE commit, in the same job
<apply the change>
scripts/bench --check     # -> "ok: 106 comparisons within thresholds"
git checkout crates/kernel/benches/baseline.tsv
```

Do not commit the furnace-recorded baseline.

**Refutation 2 — the x86 module workload has one working route, not two.**
`HEATHER_FUNCTION_IR_X86_DUMP` writes the generated module, but
`heather check` of that file against a `-L` directory of symlinks named for its
imports reports one error: the module is only checkable inside the test
harness's own module base. Use `scripts/measure-x86-conv-miss` (or the test
binary directly with `HEATHER_FUNCTION_IR_X86_NODES=5 HEATHER_TIMINGS=-`, which
is what §3's numbers came from — the switch was `HEATHER_FUNCTION_IR_X86_TIMINGS`
before the instrumentation layer was consolidated,
`docs/instrumentation-design.md`) and read the `kernel_gate_ns` column of the
module row. `HEATHER_FUNCTION_IR_X86_VALUE_METRICS=1` adds the
sampler's own clocks and inflates the kernel column by ~50%; keep it off for
timing and on only for attribution.

A third, smaller note: `perf` is not installed on the furnace image, so
`HEATHER_FUNCTION_IR_X86_PERF` produces nothing there. The 2026-09-06 profile
percentages in the issue were not re-taken in this round; §1 re-derives the
attribution from allocation counts instead, which is why it is stated as counts.

## 6. Verification items for the implementing pass's first hour

Cheap checks that would refute this design if it is wrong. Run them before the
timing work, not after.

1. **`push_tele` really installs a fresh cache.** Add a kernel test that checks
   a binding whose body pushes a telescope and then unfolds a global whose index
   means different bindings before and after the push. If the cache leaks across
   `push_tele`, this is the shape that returns the wrong body. `Env::push_tele`
   in `typing.rs` and in `conv.rs` must agree; a `debug_assert` that the two Ψs
   are not `same_identity` is not enough on its own but is a cheap tripwire.
2. **The differential oracle still agrees.** `crates/kernel/tests/conv_differential.rs`
   and `eval_differential.rs` decide the same verdicts through the rewriter,
   which after this change shares the checker's cache on the `Tc::whnf` path.
   These are the suites that would catch a body rescoped at the wrong index.
   The prototype with the shared cache on **by default** was already run
   through `scripts/test --fast` in this round: **2409 passed, 0 failed, 5
   ignored**, the same counts as the unmodified tree the same day, and
   1089 s of reported target time against the same 1089 s
   (`issues/certgen-harness-cost.md`, 2026-09-11). That is the strongest
   verdict-neutrality evidence this design has; reproduce it first.
3. **The `value-metrics` counters still attribute per gate.** `arenas` must
   still equal the query count (11 671 on the five-node module) and the
   per-item `ValueMetricsSnapshot`s must still sum to it. Lever 1 changes no
   arena's lifetime, so any movement in `arenas`, `env_nodes`,
   `term_closures` or `type_closures` means something else changed.
4. **`Tc::conv_memo`'s aliasing invariant is untouched.** Nothing in this design
   recycles storage, so "identity keys own every `Rc` they identify" still
   holds by construction. Confirm by inspection that no `ConvMemo` field gained
   a borrow — if the answer needs a test, the design has drifted.
5. **The public conversion API is byte-identical.** `git diff` should show no
   change to the signatures of `conv_type`, `conv_term`, `conv_local_ctx`; a
   change there means the elaborator was dragged in and the round grew.
6. **A negative control on the win.** Build with the shared cache and confirm
   the five-node module's kernel column *does* move ~12%. If it moves by less
   than a few percent, the cache is not being shared (most likely because an
   `Env` literal was missed and each query is still building its own), and the
   timing work should stop until the counters say otherwise.

If the bar in §5 fails after all six pass, **stop and report**: the remaining
cost is §2's 1.94 M `Rc` allocations, and it is a different round.

## 7. Amendments from the implementing pass (2026-09-11)

Written by the pass that built §3, in place, against `furnace-bb0218be4a`
(EPYC 9J14, 16 cores). Nothing below changes the design's shape; each line says
what it amends and why implementing forced it.

**Amends §3 (`Env::new_with`'s argument).** `conv::Env::new_with` takes
`bodies: Rc<BodyCache>`, not `Option<Rc<BodyCache>>`: the cache is
unconditional now, so `Env::new` delegates with a fresh one and the `Option`
had no second inhabitant. The prototype's `Option` was the env switch.

**Amends §3 (the entry points).** `conv_type_with_metrics` and
`conv_local_ctx_with_metrics` are **deleted**, not kept beside the four cached
entries: `typing.rs` was their only caller, so leaving them was dead code in
every configuration. For the same reason `conv_type_cached` and
`conv_local_ctx_cached` carry `#[cfg(not(feature = "value-metrics"))]`,
mirroring the `cfg` on typing's import — without it each configuration builds
one unused function. The four names and their arities are as §3 specifies.

**Amends §6 item 1 (where the test lives).** The test is
`typing::memo_tests::a_telescope_push_rebuilds_the_body_cache`, beside the
memo tests as suggested, because the shape it needs — warm the cache at a Ψ-index,
push, ask again at the same index — reaches `Env::push_tele` and `Tc::whnf`
directly and no public term shape pushes a telescope over two *bodied*
definitions. Ψ is two `Ty 0` definitions, so index 1 is `⌜Nat⌝` before the push
and `⌜Unit⁰⌝` after it. It has a negative control: with `push_tele` inheriting
the cache instead of rebuilding, it fails with `left: Ok(Nat) right: Ok(Unit 0)`.

**Amends §4 (the retaken column).** Same box, one job, `--save` before and
`--check` after, the three module repetitions run warm (the first repetition of
each state carries its build and is excluded, as the design's own column was):

| row | before | after |
|---|---|---|
| module `mixed ALU kernel=` | 0.999 / 0.995 s | 0.883 / 0.893 s (−11%) |
| module `mixed ALU total=` | 1.722 / 1.715 s | 1.611 / 1.628 s (−5.5%) |
| module peak RSS | 541.9 / 543.0 MB | 542.4 / 535.9 MB |
| Omega cold release wall | 10.22 / 10.21 / 10.29 s | 9.89 / 9.79 / 9.88 s (−3.3%) |
| Omega peak RSS | 196.1 / 197.6 / 195.9 MB | 194.7 / 194.4 / 195.8 MB |
| module queries / `arenas` | 11 671 | 11 671 |
| `type_cache_inserts` / `term_cache_inserts` | 1 894 881 / 49 249 | 1 894 881 / 49 249 |

`env_nodes`, `term_closures` and `type_closures` are identical to the digit
before and after (1 620 830 / 2 312 408 / 2 715 984), which is §6 item 3's
verdict: no arena's lifetime moved. `scripts/bench --check` against the
before-state `--save` on the same box: `ok: 106 comparisons within thresholds`,
every slope unmoved.

**Amends §5 refutation 1 (restoring the baseline).** The furnace's checkout is
not a git repository, so `git checkout crates/kernel/benches/baseline.tsv` does
not run there. Copy the desktop baseline aside before `--save` and move it back
after `--check`; `git apply`/`git apply -R` work outside a repository and are
how the one job reached both states.
