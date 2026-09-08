# Benchmarking the kernel: the cost model, and what "regressed" means

The kernel is the trusted basis, so it stays **simple**: the bootstrap depends
on it being small enough to trust and re-check. That constraint decides what
this suite is for. The answer to a slow number here is almost never "make the
kernel cleverer" — it is to know the cost model, keep it stable, and notice
when it changes. Consistent measurement is the substitute for complexity.

Owning issue: `issues/kernel-benchmarks.md`. The frontend has a separate
suite for a separate question (`issues/frontend-benchmarks.md`,
`docs/frontend-benchmarking.md`, `scripts/bench-frontend`): there, user
latency; here, the cost model. That suite's harness is a sibling of this
one's rather than a shared crate, and its doc says which four things differ
and why each of them is one of the differences between the two questions.

## Running it

```
scripts/bench                        # measure and print
scripts/bench --check                # compare against the recorded baseline; exit 1 on a regression
scripts/bench --save                 # record a new baseline
scripts/bench --quick --filter nat   # iterate on a fixture (shapes only)
scripts/bench --list                 # what is in the suite
scripts/bench --stack-only           # only the stack probe (usable in a debug build)
```

For evaluator allocation/cache diagnosis rather than timing, selected
elaborator acceptance tests honor `HEATHER_VALUE_METRICS=1` when built with
`--features value-metrics`, and print an explicit `ValueMetricsSnapshot` under
`-- --nocapture`. The current probes are
`lib_std_bitvec`'s machine-width carry test, `x86_64`'s module check, and
`certgen`'s `add` generation. Always invoke them through `scripts/test`; the
feature and environment flag change observation only, not fuel, cache capacity, or the
checked program. These counters are the stable evidence for working-set shape;
wall times from such a diagnostic run remain issue-log data, not baselines.
The same flag makes `heather check` (built with `-p heather-cli --features
value-metrics`) print one snapshot per checked module, which is the quickest
way to read the working set of a single probe theorem: reset before each
module, so the root module's line excludes its imports.

**Always through `scripts/bench`, never bare `cargo bench`** — same rule as
`scripts/test`, and for a sharper reason: benchmarks deliberately push
reduction and conversion at size, which is precisely the workload that turns a
wrong bound into an unbounded normalization. The wrapper is where the `ulimit`
lives.

A full run is a few minutes. `--quick` is for iterating on fixtures; its
numbers are shapes, not measurements, and `--save` warns if you record them.

## What gets reported

Three kinds of number, in decreasing order of how much they should be trusted
across machines.

**1. The scaling exponent** — the log-log slope of time against the family's
work unit, printed under each family. This is the headline, because it is the
machine-independent part: absolute times differ several-fold between a laptop
and a CI runner, while "substitution is linear in term size" either holds or is
a bug. Families that make a claim about their exponent declare an expected
band, and `--check` fails when the fit leaves it *whether or not a baseline
exists on this machine*.

**2. Stack per level** — measured, not timed. `stack/check-numeral` bisects the
deepest numeral that `check_term` survives on a thread of exactly 4 MiB, by
re-executing the bench binary as a child process (an overflow cannot be caught;
it can only be survived by someone else). Frame sizes come out of codegen, so
this number is comparable across machines with the same toolchain and profile,
and wildly different between profiles — see below.

**3. Absolute times** — min of several rounds, with the median printed
alongside. The minimum is the right statistic for deterministic work: every
sample measures the same computation plus non-negative interference, so the
smallest is the least contaminated. A large min/median gap means the machine
was busy, and the report flags it (`⚠ noisy`). `--check` compares times only
when the baseline's `host` and `profile` match.

## What "regressed" means

`scripts/bench --check` fails on any of:

| condition | threshold | why that threshold |
|---|---|---|
| a case is slower than baseline | ≥ 1.25× | measured run-to-run spread on the recording machine is ~1–4%; 1.25 tolerates a merely-busy machine, because a gate that cries wolf gets ignored |
| a fitted slope drifted upward | > +0.35 | a 4-point fit over a 16× size range moves ±0.15 between runs; 0.35 catches linear → quadratic with margin |
| a slope left its declared band | — | the band is a standing claim about the cost model, checked on every machine |
| the stack probe lost depth | > 10% fewer levels | bisection is exact to one level; 10% is "not a one-frame rounding change" |

Improvements ≥ 20% are printed too, as a hint to re-record — not a failure.

**Re-run a single-case flag before believing it.** A lone case over the
threshold with its neighbours in the same family unmoved is usually the
machine, not the code: this happened on the first day (`nat/mul-normalize:32`
read 1.35× while 24 and 48 were fine, and three quiet re-runs came in 4%
*under* baseline). A real regression moves a family, not one point in it.
`--filter <family> --check` is the cheap way to ask again.

When a regression is real and intended, `--save` and say so in the commit.
When it is real and *not* intended, it files an issue: this suite does not own
optimizations, only measurements (`issues/README.md` rule 3).

## The baseline file

`crates/kernel/benches/baseline.tsv`, tab-separated so it stays greppable and
diffable, and parseable without a dependency. Rows are `env` (host, cpu,
profile, rustc, commit), `case` (family, size, min ns), `slope`, and `stack`.
Being in the tree is the point: a baseline that lives in CI artifacts is a
baseline nobody compares against by hand.

Re-record when the machine changes, the toolchain changes, or a deliberate
change moves the numbers. Time comparability is keyed on cpu + profile +
rustc — not the hostname, which is the one env row with no bearing on speed
(a machine rename once turned the time half off silently while `--check`
kept printing `ok`; `issues/frontend-bench-baseline-host-string.md`). A
baseline from another machine is still useful — the slope comparisons run
regardless — but a run that skipped its time half says `shape-only` instead
of `ok` and exits 3, so a scripted gate cannot mistake it for a full pass.

## Why no Criterion

`issues/dependency-policy.md` keeps the kernel at an audited minimum. Its one
small shipped dependency does not justify adding Criterion's much larger
dev-only graph to the same lockfile and audit surface. What Criterion buys —
bootstrapped confidence intervals, outlier classification, plots — is aimed
at detecting small differences in noisy code. This suite is aimed at a cost
model: shape, and order-of-magnitude changes in deterministic tree walks. A min-of-samples
estimator in ~250 lines answers that, and the harness is small enough to read
in one sitting (`crates/kernel/benches/kernel/harness.rs`).

## Fixture rules

Two, and both have been paid for elsewhere in this tree:

- **Setup is not timed.** Terms, contexts and expected answers are built when
  the family is constructed. `Case::run` makes the kernel call and nothing
  else.
- **A fixture validates before it is timed.** Each case carries a cheap
  checksum the harness verifies once, and the heavier structural assertions
  (this checks; this reduces to that; `mirror (mirror t) ≡ t`) run at setup.
  The failure mode is specific: a fixture that stops doing its work gets
  *faster*, so an unvalidated benchmark reports a win for a bug.

## What is in the suite, and why each is there

| family | measures |
|---|---|
| `subst/shift-local` | one full pass over a term, no replacement — the suite's floor for "what does a traversal cost" |
| `subst/apply-local` | the same pass with replacement; the gap is what substitution adds |
| `nat/step-once` | **one** `elim_Nat` β-step against annotation size the rule never reads. Expected exponent zero — the sharpest fixture here |
| `nat/add-normalize` | the kernel *executing* a program: `n` β-steps, then reading a numeral off |
| `nat/mul-normalize` | quadratic by construction — the control that proves the fit distinguishes exponents |
| `nat/check-numeral` | the checking walk of `issues/numeral-stack-depth.md`, timed |
| `conv/computed-numeral` | an equation discharged purely by computation — the thesis-shaped fixture in miniature |
| `conv/perturbed-pairs` | conversion over the generated well-typed corpus: representative shapes, not chosen ones |
| `wf/check-tree` | reading branching data — `Vec`/`Fin` unfolding per constructor |
| `wf/mirror-involution` | `Wf` elimination at depth, twice, then compared |
| `code/check-identity-recursor` | the 45-branch code recursor: the largest single thing the checker sees (a fixed cost, ~0.54 ms) |
| `code/whnf-identity-recursor` | branch instantiation per code node — the marginal cost of recursion over code |
| `check/generated-terms` | checker throughput over the generated corpus |
| `stack/check-numeral` | bytes of stack per level of a recursive walk |

Numerals are sized past 150 deliberately: 150 is the largest numeral the
*elaborate-then-check* path admits today (`issues/numeral-stack-depth.md`),
nothing caps them in the kernel, and these families are what will show whether
lifting that cap costs anything.

What is **not** here: checking the declarations the tier-1 lowering emits.
Those come from `elab`, which sits above the kernel and cannot be reached from
a kernel bench; `docs/frontend-benchmarking.md` now has that number, and it
is larger than this suite's framing suggests — on `lib/ir_v1.hthr` the kernel
gate is **98.8%** of the wall clock, and the frontend suite's forded families
are cubic in a constructor count for the same reason (a term the elaborator
emits, re-checked by a kernel that has no definitions).

Also not here, and for a sharper reason: the arm-nested probe of
`issues/whnf-sharing-term-growth.md`, which lives in `scripts/probe-whnf-sharing`
and is driven through the release CLI. Four hand-built kernel reconstructions
of that shape have now measured **linear** (three in
`docs/nbe-conversion-design.md` §12, a fourth in stage 0's log) while the
elaborated original doubles per level: small kernel terms keep their sharing
through `subst.rs`'s depth-zero fast path, so the exponent needs the
elaborator's binder depth and term bulk to appear at all. That probe is a
ratio between adjacent levels rather than a slope, it takes minutes rather
than milliseconds, and it is run deliberately — it is not part of
`scripts/bench` and `--check` does not know about it.

## Profile matters more than you would guess

The stack probe, same code, same machine, 4 MiB thread:

| profile | deepest numeral | per level |
|---|---|---|
| release (`scripts/bench`) | 1414 | 2.9 KiB |
| debug (`scripts/bench` build, run with `--stack-only`) | 76 | 53.9 KiB |

An 18× difference in frame size. It explains the ~47 KB/level of
`issues/numeral-stack-depth.md` — that figure is a *dev-profile* figure, which
is the profile `scripts/test` runs in, so it is the one that binds for tests
and the one a numeral in a test hits. It also means the kernel's real
per-level stack cost in a shipped checker is far smaller than that issue's
headline. Both numbers are true; they answer different questions.

To reproduce the debug figure:

```
cargo build --benches                       # dev profile
ulimit -v 4194304
./target/debug/deps/kernel-*  --stack-only
```

## Adding a family

In `crates/kernel/benches/kernel/fixtures/`, return a `Family` with a stable
`name` (`area/fixture`, since baseline keys are built from it), a work `unit`,
cases at increasing sizes, and an `expect_slope` band **only** if the exponent
is a claim. Two cases where it is not, both in the suite: a size axis that is a
case count (`conv/perturbed-pairs` — a slope of 1 would be arithmetic, not a
property of the kernel), and a family dominated by a fixed cost
(`code/check-identity-recursor`, where the fit is ~0 and says nothing).

When a band records a defect rather than a design, say so in the doc comment,
with the issue link and the band it becomes when fixed. Recording the exponent
that exists is deliberate: a permanently red gate is a gate nobody reads.

## The loop, once, end to end

The first run of this suite found that substituting a payload deep-copied it
three times even at depth zero
(`issues/subst-copies-payloads-at-depth-zero.md`, since fixed), and the round
trip is what the suite is for:

1. `nat/step-once` — added to isolate the suspicion: one `elim_Nat` β-step,
   timed against annotation size the rule never reads. 154 µs at 1024 nodes,
   slope 1.03. A cost model claim (O(1)) contradicted by a number.
2. Three bands were set to the exponents that *existed* (2.02, 2.77, 2.20),
   each naming the issue and the band it would become. The suite stayed green,
   which is the only way it stays read.
3. The fix — a `by == 0` guard on the shift entry points, sound by a law
   `tests/subst_laws.rs` already checked — turned `--check` red, on exactly
   those bands and nothing else. Five "regressions", all of them the old
   exponents being left behind.
4. `--save`, and the bands became the new claims.

| | before | after | and after the sequel |
|---|---|---|---|
| one β-step, 1024-node annotation | 154 µs | 98 ns, flat | — |
| `add n n`, n = 1024 | 232 ms | 171 µs | 178 µs |
| `conv(add n n, 2n)`, n = 512 | 92 ms | 154 µs | 151 µs |
| `mirror (mirror t)`, 2963 nodes | 262 ms | 89 ms | **30 ms** |
| one β-step into a 1024-node closed body | — | 51 µs | 20 µs |

The `mirror` row is the one to take a lesson from twice. Nobody was looking at
`Wf` elimination, and it got 3× faster from a fix aimed at numerals, because
the fixture set was wide enough to show the defect was not about numerals. Then
profiling *that* row found the sequel
(`issues/subst-rebuilds-unchanged-subterms.md`) — substitution rebuilding
closed annotations — worth another 3× on it and 1.3–1.5× across checking and
conversion generally.

Each round also left its own follow-up filed rather than assumed: the exponent
bands say which numbers are claims and which are records, and
`issues/subst-visits-closed-subtrees.md` states the trigger for the next step
instead of taking it.
