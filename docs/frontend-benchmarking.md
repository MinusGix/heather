# Benchmarking the frontend: user latency, and what "regressed" means

The kernel suite guards a **cost model** (`docs/benchmarking.md`). This one
guards a **wait**: the time between saving a `.hthr` file and knowing whether
it checks. The elaborator is allowed to be clever — it is not the trusted
base — so the answer to a slow number here *may* be "make the elaborator
cleverer", which is the opposite of the kernel suite's answer and the reason
the two suites are separate.

Owning issue: `issues/frontend-benchmarks.md`.

## Running it

```
scripts/bench-frontend                          # measure and print
scripts/bench-frontend --check                  # compare against the baseline; exit 1 on a regression
scripts/bench-frontend --save                   # record a new baseline
scripts/bench-frontend --no-heavy               # skip lib/certgen/ir_v1.hthr — the fast loop
scripts/bench-frontend --quick --filter forded  # iterate on a fixture (shapes only)
scripts/bench-frontend --list                   # what is in the suite
```

**Always through `scripts/bench-frontend`, never bare `cargo bench`** — the
rule CLAUDE.md states for every direct `heather` run, for the same reason:
whole-file checking is memory-superlinear (an uncapped release check of a
deep-fuel IR theorem reached ~22 GB), and this suite checks the heaviest file
in the tree *and* sweeps the forded families towards the fuel cliff of
`docs/inductive-fording-lowering.md` §14.9. The wrapper is where the `ulimit`
lives: 8 GiB of address space, 30 CPU minutes.

A full run is ~4 minutes and three of them are `lib/certgen/ir_v1.hthr`. `--no-heavy`
is ~40 seconds and is what to run while iterating; `--quick` on top of that is
seconds, and its numbers are shapes, not measurements.

## What gets reported

Four kinds of number, in decreasing order of how much they should be trusted
across machines.

**1. The scaling exponent** — the log-log slope of time against the family's
work unit. The headline, for the kernel suite's reason (machine-independent),
and empirically the most robust thing here: across three full runs on a
machine under varying load the absolute times moved by up to 1.5× while the
fitted exponents moved by ≤0.25, and by ≤0.1 on all but the noisiest family.
Families that make a claim declare a band, and `--check` fails when the fit
leaves it, whether or not a baseline exists on this machine.

**That ±0.25 is a loaded-machine figure and it is far too pessimistic to size
a band with** (measured 2026-08-17, `issues/frontend-benchmarks.md`, which
owns the bands and carries the numbers): repeated back-to-back runs on a
machine carrying nothing but a desktop put the whole run-to-run *range* of
every family's fit in the low hundredths. So a fit that sits a few hundredths
outside its band is not the machine, and a band boundary within a few
hundredths of the measurement is not a claim about the cost model — it is a
coin toss, and it was one on two families until that day. Bands are therefore
recorded as **the measurement ±0.35**, the same distance `--check` calls a
slope drift, so the band gate and the drift gate agree about what "moved"
means.

A band can be left on **either** side, and the two mean opposite things.
Above: the cost model got worse — that is the regression a round should
suspect itself of. Below: the code became cheaper than the recorded claim, so
the *claim* is what is broken, and the fix is to re-record the band rather
than to change any code. `--check` fails on both, because a false claim is
false in both directions and a band nobody re-records is a band that stops
meaning anything — but it prints which side, because the two want different
work.

**2. Latency budgets** — an absolute ceiling on a corpus file, checked on
every machine, baseline or not. `lib/certgen/ir_v1.hthr` is the one that matters:
59 s through the release CLI on a quiet machine, 67–88 s from this harness
depending on what else the machine was doing, budget **150 s**. It is not
derived from the baseline — a budget that moves with the recording is not a
budget — and it is deliberately loose, because what it is for is "the
library file now takes five minutes", not
"the library file got 30% slower". That second question is the baseline's.

**3. The phase split** — parse / elaborate / kernel gate, printed under every
case that reports one and recorded in the baseline as `split` rows. Its job is
to make a regression **name its layer**, so it is never a failure on its own:
`--check` prints moved phases under the case they belong to, tagged `where`.

The split is measured on one instrumented run (the same run that validates the
fixture), not min-of-rounds, because attributing the parse costs an extra
parse and that must not happen inside a sampled round. Read it as proportions,
not as a measurement.

What the three phases mean exactly:

| phase | what is in it |
|---|---|
| `parse` | `heather_syntax::parse_file`, timed on its own pass |
| `kernel` | the `typing::check_type` + `check_term` **gate** that every finished declaration passes (`crates/elab/src/stats.rs`) — all three gate sites, `gate.rs`'s list being the authority: an ordinary declaration, a `meta fn`, and a **generated** definition |
| `elab` | the residue: everything the elaborator did, **including its own conversion and whnf calls into the kernel** |

The three phases are now three of the registry's named timers
(`docs/instrumentation-design.md`): `stats::kernel_ns` still means exactly
what this table says, and the bench's split is unchanged, but the same
brackets also feed the finer per-declaration columns that
`heather check --timings` dumps — unification, trait resolution, match
speculation, generated-declaration emission, the omega stages, image decode,
replay and publication, cache hashing. When a `parse`/`elab`/`kernel` split
says *which layer*, the dump says which declaration and which phase inside
it.

That last row is the one to remember. The elaborator calls the kernel while
it works — unification, `whnf`, `conv_type` — and those calls are on the
*elaborate* side, because they are elaboration deciding something rather than
the kernel re-checking a result. `kernel` is the gate and only the gate.

**4. Absolute times** — min of several rounds, with the median printed
alongside. Min is the right statistic for deterministic work (see the kernel
doc). Rounds are adaptive: a case whose single round costs over a second gets
3, over ten seconds gets 2, and the report prints the count, so a two-round
number is never mistaken for a seven-round one.

## What "regressed" means

`scripts/bench-frontend --check` fails on any of:

| condition | threshold | why that threshold |
|---|---|---|
| a case is slower than baseline | ≥ 1.25× | the kernel suite's number, kept for consistency — but see the noise warning below, which matters far more here |
| a fitted slope drifted upward | > +0.35 | as the kernel suite. The 0.25 spread this row used to cite for `forded/declared-index-tags` was measured under load ~10; on a quiet machine that family's six-run range was 0.06, so a lone slope flag is worth a re-run but not a shrug |
| a slope left its declared band | — | a standing claim about the cost model, checked on every machine |
| a case exceeded its latency budget | — | a standing claim about the wait, checked on every machine |
| a case blew its guard | 3× its budget | it was measured once and not sampled; something is very wrong or the fixture needs a new home |

Improvements ≥ 20% are printed too, as a hint to re-record.

**The noise warning.** Frontend cases are 10³–10⁶ times longer than kernel
cases and run correspondingly fewer rounds, and the recording machine on
2026-08-04 was carrying a load average of ~10 with the CPU at 96 °C. Under
those conditions consecutive full runs disagreed by up to **1.5×** on
individual cases — including cheap, many-iteration ones like
`corpus/prelude:build`. So the kernel doc's rule ("re-run a single-case flag
before believing it") is not a footnote here, it is the primary reading
instruction: a regression that moves *a family* is real, a regression that
moves one point while its neighbours sit still is the machine.
`--check` helps by printing `[med/min 1.4×]` beside any case whose own median
sits well above its own min — that annotation means the machine was busy
*during this run*, so the flag beside it carries no weight.

`--filter <family> --check` is the cheap way to ask again; `--no-heavy` makes
it cheaper.

**Interim protocol for the time half** (2026-08-17,
`issues/frontend-bench-heavy-contaminates-cheap-cases.md`): read the absolute
times from a `--no-heavy` run. A full run's heavy `lib/certgen/ir_v1.hthr` cases leave
the process in a state that makes later families read 1.3–1.5× higher —
measured by controlled experiment, not inferred: the same families are green
under `--no-heavy` and under `--filter` in the same minute a full run flags
them. That is above the 1.25× threshold, so a full run's cheap-case time flags
carry no information until that issue is fixed. Everything else the full run
gates — slope bands, latency budgets, guards, and the heavy cases' own times,
which are seconds-scale and unaffected — is trustworthy and is the reason to
run it.

## The baseline file

`crates/elab/benches/baseline.tsv`, tab-separated for the kernel suite's
reasons (greppable, diffable, parseable without a dependency). Rows are `env`
(host, cpu, profile, rustc, commit), `case` (family, label, min ns), `split`
(family, label, phase, ns) and `slope`. The key is a **label**, not a size —
corpus cases are named by file.

Re-record when the machine changes, the toolchain changes, or a deliberate
change moves the numbers. Time comparability is keyed on cpu + profile +
rustc — not the hostname, which is the one env row with no bearing on speed
(a machine rename once turned the time half off silently while `--check`
kept printing `ok`; `issues/frontend-bench-baseline-host-string.md`). A
baseline from another machine still gates slopes, bands and budgets, but a
run that skipped its time half says `shape-only` instead of `ok` and exits
3, so a scripted gate cannot mistake it for a full pass.

> **The baseline in the tree was re-recorded 2026-08-17** on an otherwise idle
> machine (`issues/frontend-benchmarks.md` has the run's conditions, every row
> that moved, and the evidence that the heavy rows moved because the system got
> faster rather than because the fixture stopped working — the corpus checksum
> is a count of declarations landed, so that is checkable without a clock).
> Every recorded time here is superseded by it; the rows below and in the
> historical sections are what those rounds measured on their day, kept because
> the *shapes* and the reasoning are what they are for, and per the
> numbers-in-docs policy on
> `issues/perf-tracking-consistent-environment.md` current figures live on the
> issue rather than here. Read absolute times from a `--no-heavy` run until
> `issues/frontend-bench-heavy-contaminates-cheap-cases.md` closes.

## Why no Criterion, and why a second harness at all

Same answer as the kernel suite for the dependency (`issues/dependency-policy.md`,
and what Criterion buys is aimed at small differences in noisy code — this
suite's differences are 1.5× and up). The harness is a sibling of the kernel's
rather than a shared crate because four things differ, and each of them is one
of the differences between "cost model" and "user latency": labels instead of
sizes, the phase split, per-case guards and budgets, and no stack probe.
Sharing them would mean a harness with two modes and a set of options that
mean nothing in one of them.

## Fixture rules

The kernel suite's two, inherited:

- **Setup is not timed.** Sources are generated, prelude'd elaborators built,
  and every generated source *validated by elaborating it*, when the family is
  constructed. Fixture construction is where this suite's seconds actually go,
  which is why `--list` does not build fixtures and why the smoke test builds
  only the smallest case of each family.
- **A fixture validates before it is timed.** Every generated source must
  check cleanly at setup, and every case carries a checksum the harness
  verifies. A fixture that stops doing its work gets *faster*.

And one of its own:

- **A timed run must be repeatable, and `check_source` mutates.** So every
  run needs a fresh elaborator, and there are two honest ways to get one:
  rebuild the prelude or clone a prelude'd one (both numbers are in the
  report, as `corpus/prelude`; the clone is the cheaper by orders of
  magnitude, though the ratio has narrowed as the elaborator grew —
  `issues/prelude-clone-cost-grew.md` tracks it). The corpus rebuilds,
  because that is what `heather check <file>` does per file and the corpus
  number is meant to be the number a user waits for. Generated families
  clone, because a fixed build cost of the same order as the smallest
  fixture does not merely add noise to the fit — it *flattens the
  exponent*, which is the number this suite reports.

Generated fixtures are generated in memory, not committed as `.hthr` files: a
swept family is five files differing in a loop bound, so committing them
commits the generator's output instead of the generator. The committed
`.hthr` files stay what they are for — real proofs, in `lib/`.

## What is in the suite, and why each is there

Numbers below are the recorded baseline (2026-08-05 for the forded
families, 2026-08-04 for the rest); the parenthesised ranges are what the
same fixture read across three full runs on the same machine at different
loads, which is the honest width of an absolute time here.

| family | measures | today |
|---|---|---|
| `corpus/prelude` | the per-file fixed cost the CLI pays, and the clone that the generated families use instead | 87 µs build / 108 ns clone |
| `corpus/parse` | the parser alone over `lib/*.hthr` | 6–18 ns/byte |
| `corpus/check-file` | `lib/*.hthr` end to end, as `heather check` does it, with the phase split | 0.58 ms / 1.21 s / 67 s (67–88 s) |
| `scale/declarations` | *n* independent `fn`+`theorem` pairs — file size with no pathology in it | slope 0.98 (0.98–1.12) |
| `scale/wide-inductive` | an inductive with *n* constructors and the *n*-arm `match` | slope 1.51 (1.51–1.67) |
| `forded/computed-arms` | a route-2b family with *n* constructors, and the *n*-arm match | slope 2.54 (was 2.79) |
| `forded/occurrences` | *n* declarations over one forded family | slope 1.01, ~19 ms **per use** (was ~28 ms) |
| `forded/declared-index-tags` | form A swept along the *index* type's constructor count | slope 2.62 (unmoved by two rounds — see below) |
| `forded/declared-index-branching` | the same at a **branching** index constructor | slope 1.57 (was 1.53) |
| `meta/nested-inference` | *d* nested implicit instantiations, built and projected back | slope 1.84 (1.84–1.90) |
| `rewrite/fa` | `g(f^n(a)) = g(a)` by *n* `rewrite`s with `h: f(x) = x` (mengine `rewrite_fa`). **Lower bound linear** | debt: about n² (n rewrites of an O(n) goal) |
| `rewrite/repeat-mod` | `(…(b mod p)…) mod p = b mod p` by *n* − 1 rewrites, `mod` opaque (mengine `repeat_mod`). **Lower bound linear** | debt: about n² |
| `rewrite/let-addr0` | a *k*-let chain `vᵢ = vᵢ₋₁ + vᵢ₋₁ + 0`, every `+ 0` rewritten away (mengine `addr0_let_in`). **Lower bound linear** | debt: 2^k |
| `rewrite/let-nary` | three lets `xᵢ = f(xᵢ₋₁, …)` of arity *n*, rewritten to `x₀` (mengine `rewrite_nm`). **Lower bound linear** in n·m | debt: tree-sized in elaboration |
| `let/fan` | *k* lets each using the last twice, as a `fn` body. **Lower bound linear** | met |
| `let/dep` | `fan` with an unused `refl` proof let per link. **Lower bound linear** | met (it was above quadratic while each unused value was discarded one binder deeper) |
| `let/under` | `fan` with a `λ` between every link. **Quadratic while shifts are eager**: the values the elaborator holds are Θ(k²) distinct nodes (`issues/open-payload-shift-copies.md`) | at its bound (the representation's, not linear) |
| `let/stmt` | `let-addr0`'s chain stated equal to itself, by `refl`. **Lower bound linear** | met (was 2^k: two equal DAGs compared as trees) |
| `inductive/isa-declaration` | an *n*-form instruction type with register/immediate/memory operand fields, declared. **Lower bound linear** | met (~1.0) |
| `inductive/isa-constructor-use` | four constructor values of that type. **Lower bound linear** (the declaration) | debt: ~1.7, Θ(n²) elaboration per mention |
| `inductive/isa-opcode-match` | an *n*-arm `match` into `Nat`, payloads ignored. **Lower bound linear** | debt: ~1.6, mostly elaboration |
| `inductive/isa-roundtrip` | an *n*-arm rebuild and its identity theorem (one `refl` per arm). **Lower bound linear** | debt: ~2.2, mostly gate |
| `inductive/enum-equality` | *n*²-arm decidable equality on an *n*-constructor enum, and its `refl` theorem. **Lower bound quadratic** | debt: ~2.5 |
| `inductive/record-fields` | a *k*-field record: literal, projection, rebuild, frame theorem. **Lower bound linear** | debt: ~1.4 |
| `inductive/mutual-declaration` | a ring of *m* mutual sorts, declared. **Lower bound linear** | debt: ~1.5, small |
| `inductive/mutual-recursion` | structural recursion over that group, and one `refl` unfolding. **Lower bound linear** | debt: ~2.8, all gate; out of fuel at *m* = 8 |
| `inductive/typed-syntax` | intrinsically typed terms `Tm(J(Γ, A))`, *n* constructors: `size` and two `refl` unfoldings. **Lower bound linear** | debt: ~1.8 over 5..8, and a large constant |
| `inductive/function-fields` | an `IWf`-on-`W` family of *n* function-field constructors: `size` and two `refl` unfoldings. **Lower bound linear** | debt: ~1.7 over 2..8, ~3.4 past it |

The spread is the point of the noise warning above, and it is also the
argument for the slope being the headline: the times moved by up to 1.5×
between those runs, the exponents by ≤0.25.

Since modules landed (docs/modules-design.md §7), `corpus/check-file` times
an **import closure** rather than a file: `lib/certgen/ir_v1.hthr` imports
`lib/std/num/nat.hthr`, and what `heather check lib/certgen/ir_v1.hthr` makes a user wait
for is both. The x-axis stays the root's bytes — the label names the root —
so the two `ir_v1` cases legitimately changed *shape*, not merely time, on
2026-08-05, and their baseline rows have to be re-recorded rather than
compared across that boundary.

**The closure is computed, not listed** (2026-08-17,
`issues/frontend-bench-ir-closure-stale.md`). It was a list of module names in
the fixture for two weeks, and it went stale the day `lib/std/core/bool.hthr`
gained `import logic;` — after which every module of the closure failed, since
a module whose import does not resolve never registers a scope and so breaks
the module after it too. A corpus case that fails its whole closure is *fast*,
and the checksum caught it only because the checksum is the error count. The
fixture now calls the CLI's own loader (`heather_cli::loader::load`, which is
why `crates/cli` has a `lib` target), so the closure the corpus times is
whatever the library actually imports.

No exponent is claimed for the corpus: the x-axis is source bytes across
unrelated files, and `lib/certgen/ir_v1.hthr` is not "a bigger `lib/lang/vec_code.hthr`" —
it is a file of deep proofs whose cost is conversion, not size. The printed
slope of ~5.4 there is an artefact of exactly that and means nothing.

## The forded families, and the round that re-recorded them

`forded/computed-arms`, `forded/occurrences` and
`forded/declared-index-tags` are the reason this suite was built when it was.
`issues/frontend-benchmarks.md` carried two 2026-08-04 triggers, and both
named the same lever:

- **§14.2** — `μ`, the index measure, was a whole `elim_Wf` **inlined at every
  occurrence**, because nothing named it. The family type had one, the
  eliminator instantiated it several times per arm, and a forded type inside
  another type multiplied that again.
- **§14.9** — at a *declared* index, form A additionally emitted one
  `child_projection` per child and one tag predicate per **other** index
  constructor, each itself a whole `elim_Wf`. The product of branching and a
  three-constructor index exceeded `DEFAULT_FUEL` and was pinned as a
  deliberate negative in `crates/elab/tests/indexed_route_2b_declared.rs`.

`issues/generated-term-defs.md` pulled that lever on 2026-08-04: `μ`, the tag
predicates and the child projections became **Ψ definitions**, registered once
at declaration time under machine names and referenced everywhere
(`crates/elab/src/gendefs.rs`). Before and after, same machine, same day:

| | 2 | 3 | 4 | 5 | 6 | slope |
|---|---|---|---|---|---|---|
| `computed-arms` (arms) **before** | 31 ms | 112 ms | 317 ms | 665 ms | 1.25 s | **3.39** |
| `computed-arms` **after** | 8.5 ms | 28 ms | 62 ms | 116 ms | 195 ms | **2.79** |
| `declared-index-tags` (index ctors) **before** | 18 ms | 48 ms | 104 ms | 199 ms | 328 ms | **2.65** |
| `declared-index-tags` **after** | 13 ms | 34 ms | 73 ms | 137 ms | 234 ms | **2.61** |
| `declared-index-branching` **before** | 353 ms | 613 ms | 996 ms | 1.48 s | 2.08 s | ~1.4 |
| `declared-index-branching` **after** | 116 ms | 199 ms | 310 ms | 458 ms | 645 ms | **1.53** |

and `forded/occurrences` — what one *mention* of a forded family costs a user
— went from **119 ms per use to 27–29 ms**, at an unchanged slope of ~1.0.
That per-use figure is the round's headline.

**The prediction this section used to carry was half right, and the half it
got wrong is the more interesting one.** It said the fits would fall *below*
their bands and `--check` would go red on exactly them. `--check` stayed
green: the round cut the **constant** by 4–7× on `computed-arms` and
`occurrences` and 3.2–3.7× on branching, and moved the **exponents** by 0.60,
0.04 and 0.00. The bands were wide enough to record a defect, and the defect
turned out to be *two* defects sharing one curve.

What the definitions removed is the generated **terms**. What is left is the
generated **types**: a forded family's skeleton `⟦Skel⟧` and its index type
`I` are `Type::Wf`s whose node count is Θ(constructors), and they are still
written out afresh at every occurrence — once per `sEq`, per `Lam` domain, per
`transp` annotation, per motive instantiation, of which there are
Θ(constructors). Θ(n) copies of a Θ(n) type is the residual quadratic, and the
same lever does not reach it: `GlobalBinding::Ty` has no body, so a *type*
cannot be a Ψ definition at all. `docs/inductive-fording-lowering.md` §14.11
records that as the successor seam.

The one place the exponent did move is `computed-arms`, and that is consistent
with the reading above: there the arm count multiplies both the types *and*
the eliminator instantiations, so removing one factor of the product shows up
in the slope; at `declared-index-tags` the swept quantity only multiplies the
type, so it does not.

Two other things stayed true across the round and are worth keeping: in every
forded family **94–99% of the time is the kernel gate**, not the elaborator;
and the bands here **record the exponents that exist, not the ones the design
wants**. They were tightened around the new slopes rather than moved, so the
next round is measured against what this one achieved.

The branching row, `forded/declared-index-branching`, is new: §14.9's fuel
cliff is what made it impossible before, and the fixture comment on
`declared_index_tags` (which stayed deliberately linear, so that its before
and after are the same measurement) is the pointer to why.

## The code-definition round (2026-08-05), and the family that did not move

`issues/family-types-as-code-defs.md` took the "emitted *types* still to go"
lever: `⟦Skel⟧` and `I` became **code definitions** (`D#code : Trm_c(· ⊢ Ty l)`,
`gendefs.rs::{SkelCode, IdxCode}`), emitted as `El (code^δ)` references in the
`Σ` components, `Lam`/`Pi`/`App`/`transp` annotations and motive
instantiations, with the `Σ`/`sEq` shell kept inline for the recognizer
(design doc: `docs/family-type-code-defs-design.md`). Before and after, same
machine, same day (2026-08-05, load ~3–6 — the noise warning applies to the
absolutes):

| | 2 | 3 | 4 | 5 | 6 | slope |
|---|---|---|---|---|---|---|
| `computed-arms` **before** | 8.5 ms | 28 ms | 62 ms | 116 ms | 195 ms | **2.79** |
| `computed-arms` **after** | 6.8 ms | 19 ms | 40 ms | 69 ms | 112 ms | **2.54** |
| `declared-index-tags` **before** | 13 ms | 34 ms | 73 ms | 137 ms | 234 ms | **2.61** |
| `declared-index-tags` **after** | 15 ms | 40 ms | 83 ms | 150 ms | 271 ms | **2.62** |
| `declared-index-branching` **before** | 116 ms | 199 ms | 310 ms | 458 ms | 645 ms | **1.53** |
| `declared-index-branching` **after** | 89 ms | 155 ms | 234 ms | 360 ms | 499 ms | **1.57** |

and `forded/occurrences` — the per-use figure — went from **~28 ms to
~19 ms per use** at an unchanged slope of ~1.0. `lib/certgen/ir_v1.hthr` did not
move (60.5 s against its 150 s budget; it is 99% kernel gate on deep
proofs, which this round does not touch).

**The design's headline claim is not met, and the number is recorded rather
than absorbed.** The design predicted `declared-index-tags` — the pure
measurement of the type multiplier — would drop below 2.0. It moved not at
all (2.61 → 2.62, absolutes flat within the machine's spread) while every
other forded family improved. The residual is therefore a **third defect
sharing the curve**, and this round's diagnosis: the `Supf`/`ElimWf`
**shape annotation slots**. Those slots carry the `Wf`'s *shape component*
(`term.rs:514`), not the whole `Wf`, and the registered codes name whole
types only — so the `sup_f` the declared-index inversion rebuilds per index
branch (`zj` in `forded_arm_a_decl`) still writes a Θ(n) shape into each of
Θ(n) branches, several times over (the equation domain, the motive
instantiations, the no-confusion transport). Θ(n²) survives the round
untouched. Recorded at fording doc §14.11 (closing note) and owned by
`issues/wf-shape-annotation-slots.md`.

The re-spell step the design left contingent (§3.2/phase 3) was measured
and **not** added: `elab_match` hands `forded_of_at` the *raw* scrutinee
type (its whnf is used only for the non-fording dispatches), the Σ
components arrive as references, and the recognizer rebuilds inline copies
only for the generator's structural reads — there is no re-inlined copy
flowing into emission for a respell to swap.

Bands after the round (the suite's rule — record the exponents that exist):
`computed-arms` 2.20–2.85, `occurrences` 0.70–1.30, `declared-index-tags`
2.30–2.90 (the 2.0 top the design wanted is *not* the recorded claim, for
the reason above), `declared-index-branching` 1.20–1.90.

## The other thing the phase split said on day one

> **These are day-one numbers and they have aged** (checked 2026-08-16,
> `issues/gendef-gate-untimed.md`). Both files have since been measured far
> below them — the kernel-side rounds that landed in between moved the
> absolute time by more than an order of magnitude, so the elaborator's
> *share* grew without the elaborator getting slower. The reading below is
> what survives (a proportion is not a measurement, and the leverage claim is
> the point); current figures live in that issue's log, per the
> numbers-in-docs policy on `issues/perf-tracking-consistent-environment.md`.

`lib/certgen/ir_v1.hthr`: parse **0.0%**, elaborate **1.2%**, kernel gate **98.8%**.
`lib/lang/vec_code.hthr`, a file with no deep proofs in it: parse 10.6%, elaborate
49.3%, kernel gate 40.2%.

The issue guessed that a split would tell a regression which layer it was in.
It does — and it also says that on the file that dominates the tree's check
time, the frontend is 1% of the wait. Elaborator optimizations aimed at
`lib/certgen/ir_v1.hthr` would be aimed at 1.2% of it; the leverage is entirely in
what the elaborator *emits*, which is what the forded families measure and
what the kernel definitions of `issues/generated-term-defs.md` changed — by
4–7× on the emitted terms, with the emitted *types* still to go.

## Route 1's turn (2026-08-06), and the fixture that was labelled wrong

Phase 5 of `docs/family-type-code-defs-design.md` §6: an unparameterized
route-1 indexed declaration gets a **family function**
`D#fam : Trm_c(· ⊢ Π(i : I). Ty l) := λ(i : I). elim(…; i)`, and every
occurrence of the family type is `El l (D#fam^δ i)` instead of the whole
type-valued eliminator written out again.

The suite had no route-1 family until this round, which is why route 1's
§10.3 entry carried "[[frontend-benchmarks]] is where 'acceptable' gets a
number" for two rounds without one. `indexed/arms` is that family: a route-1
declaration with `n` constructors and the `n`-arm `match` over it, swept
2–6. Measured against its own **registration-only** build — the defs
registered, no emission changed, which is design §8 phase 1's no-op
measurement point:

| `indexed/arms` | 2 | 3 | 4 | 5 | 6 | slope |
|---|---|---|---|---|---|---|
| registration only | 249 µs | 610 µs | 1.13 ms | 1.82 ms | 2.83 ms | **2.20** |
| emitting references | 216 µs | 517 µs | 980 µs | 1.65 ms | 2.57 ms | **2.25** |

The constant moves ~1.10×; **the exponent does not move**. The reason has
the same shape as the forded suite's residual: what is still Θ(n) per arm is
the *class* type — the tag spine of the `n − 1` members sharing the
successor branch — which `indexed_class_body` whnfs the reference back into
and `spine` then re-emits into every injection annotation. `D#fam` names the
whole family; nothing names a class.

**And the finding this round did not go looking for.**
`forded/declared-index-tags` is **not a forded family**. `Tw`'s constructors
state their indices as patterns (`Tw(SLeaf)`, `Tw(SBud(s))`), and
`classify_indexed_route` tries route 1 **first** — so that declaration has
never had a skeleton, a `μ`, or a form-A inversion. It is route 1 at a
declared index, swept along the index type's constructor count. Two rounds
read it as route 2b and explained its immovable exponent with route-2b
mechanisms: the 2026-08-04 round with "the index type is Θ(n) and a type
cannot be a Ψ definition", the 2026-08-05 round with a third defect in the
`Supf` shape slots of an inversion this declaration does not emit. Neither
round's lever touched it. Route 1's did, at once:

| `declared-index-tags` | 2 | 3 | 4 | 5 | 6 | slope |
|---|---|---|---|---|---|---|
| before (master, this machine) | 17.0 ms | 40.7 ms | 98.8 ms | 164 ms | 294 ms | **2.79** |
| after | 10.9 ms | 25.6 ms | 50.0 ms | 81.5 ms | 125 ms | **2.22** |

2.5× at the wide end and 0.6 off the exponent. The section above stands as
the record of what that round measured; what it does **not** stand for is
the attribution, and `issues/wf-shape-annotation-slots.md` is now supported
by `declared-index-branching` alone — which is genuinely forded, because
`BDup(s) : Bl(SNode(s, s))` repeats a variable and fails route 1.

The lesson for a fixture: **name the route the classifier picks, not the
route the source looks like.** The family's *name* is left alone here
because it is the baseline's key; renaming it is a coordinator's call.

### The baseline was NOT re-recorded, and why

`scripts/bench-frontend --check` is red, and it was already red on master
before this round: prelude `build` 2×, `declared-index-branching` 1.3–2.1×,
`meta/nested-inference` 1.3× — none of which this round can reach, all of
which accumulated over the ~10 commits since the baseline's `commit 1878f11`
was recorded. A re-record now would silently adopt them.

Worse, the machine is not quiet: load ~5–7 from unrelated processes and
Tctl 95 °C during the runs, and families this round cannot touch
(`scale/declarations`, `corpus/prelude`) drifted 1.5–2× *between two runs an
hour apart*. Per this document's own noise warning the absolutes above are
context and the slopes are the headline — and per design §9 the re-record
belongs on a quiet machine. So: bands updated in the fixture sources
(`declared-index-tags` 2.30–2.90 → **1.90–2.60**, `indexed/arms` recorded at
**1.90–2.60**), baseline file untouched, `indexed/arms` still `untracked`
until someone re-records. That is the deviation this round is flagging, not
absorbing.

## The rewriting and let fan-out families (2026-10-26)

`issues/tactic-scaling-bench-families.md` added seven families
(`fixtures/rewriting.rs`): mengine's four rewriting benchmarks
(`docs/mengine-survey.md` §7) and three let chains from
`issues/proof-let-substitution-cost.md`. Every one has a **linear lower
bound**, so on these families the bands are a record of debt rather than of
a design's claim: a slope above 1 is the distance to the lower bound, and the
round that closes it re-records the band from below. `let/fan` sits at its
lower bound since the kernel's typing memo, `let/dep` since unused values
are discarded at the block's depth, and `let/stmt` since `==` on terms
compares a pair of shared nodes once
(`issues/kernel-equality-walks-dags-as-trees.md`), which re-swept it over
32..256.

`let/under` (added 2026-10-26) is the exception: its bound is quadratic, not
linear, for as long as a shift is an eager copy. Each link is elaborated one
binder deeper than the last, so link `i`'s value holds every earlier link
shifted by its distance, `i` terms with distinct free indices; summed over
the chain that is Θ(k²) distinct nodes, and no memo can share nodes that are
not equal. Its band records the quadratic. Going below it is the
representation change `issues/open-payload-shift-copies.md` keeps deferred.

Three things differ from the older families:

- **Some are exponential.** A log-log fit of 2^k is not a constant, so the
  band of `rewrite/let-addr0` (and `let/stmt`'s, before its fix) is the fit over exactly the
  sizes swept, and is wider than ±0.35, because the steeper the curve, the
  more a fixed cost at the small end moves the fit. Their band's job is to
  notice the fix, which drops the slope to about 1.
- **The bands were recorded on a 4-core cloud box** (four runs each; the
  band is the mean ±0.35 or the four-run range, whichever is wider), and only
  their `slope` rows are in the baseline. Times recorded there would sit
  under another machine's `env` rows, so the `case` and `split` rows wait for
  the next `--save` on the recording machine, and until then the cases read
  `untracked`.
- **The phase split is the point.** Where the cost sits differs by family:
  the gate dominates `rewrite/fa` and `rewrite/repeat-mod` (consistent with n
  nested `J`s, each over an O(n) motive), elaboration dominates
  `rewrite/let-nary` (and dominated `let/dep` until its fix), and `let/stmt`
  split about evenly between the gate and elaboration while it was 2^k. The
  issue's log has the numbers.

Two Heather limits shape the fixtures. `rewrite` rewrites one instance per
equation (`docs/equation-rewrite-design.md` §6.1), so a family is *n*
equations in one `rewrite(h, …, h, refl)`. And the goal `f(f(…f(a)))` is *n*
nested calls, which at n = 256 exceeds the elaborator's expression depth
limit (512), so `rewrite/fa` and `rewrite/repeat-mod` stop at 128. And the opaque operations
and lemmas are theorem parameters, so that no conversion can close a goal
the rewrite was meant to close.

## The large and intricate inductive families (2026-10-26)

`issues/intricate-inductive-bench-families.md` added ten families
(`fixtures/intricate.rs`) for the two ways a declaration gets big. **Wide**:
an instruction-set-shaped type, hundreds of forms with operand fields of
other declared types, split into the phases of its life so a slope names
the phase that grows — declaring it, mentioning a constructor, an opcode
`match`, a rebuild-and-identity roundtrip, an *n*²-arm decidable equality,
and a wide state record. **Intricate**: few constructors, but the lowering
multiplies them — a mutual group of syntax sorts (declared, then recursed
over), intrinsically typed terms indexed by a judgment, and a family with
function-field children.

The conventions are the rewriting families': each family states its lower
bound (all linear but `enum-equality`'s, which is the arm count), the bands
are the mean of three cloud-box runs ±0.35 and record debt, and only `slope`
rows go into the baseline, so the cases read `untracked` until a `--save`
on the recording machine.

What the round found, each with a cheap control that does not pay it, and
each filed:

- **A constructor value costs Θ(n²) in the type's constructor count**, in
  elaboration, whichever constructor: `respell_spine` compares every
  component of the spine against the registered one by deep equality
  (`issues/wide-inductive-constructor-mention-cost.md`). The gate adds
  Θ(k·n) for the *k*-th constructor.
- **Mutual recursion is ~m^2.8, nearly all gate**, and an eight-member
  group's one-step `refl` runs out of fuel; the same constructors as one
  inductive are three orders of magnitude cheaper
  (`issues/mutual-group-recursion-gate-cost.md`).
- **Typed-syntax and function-field recursion are superlinear and gate
  bound**, with a large constant even for a `refl` of a three-node closed
  term; a plain child instead of a function field is well over an order of
  magnitude cheaper
  (`issues/indexed-family-recursion-gate-cost.md`).

The sizes stop where a family costs a few seconds per run, which on the
intricate families is early — five members, eight constructors — so their
fitted slopes understate the curve past the sweep (the issues carry the
larger CLI points). One language limit shapes a fixture: a family takes one
index (`docs/inductive-indexed-lowering.md` §8.4), so typed terms are
indexed by a declared judgment type `J(Γ, A)` (with a second constructor,
since an index type needs two).

