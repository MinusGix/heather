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
scripts/bench-frontend --no-heavy               # skip lib/ir_v1.hthr — the fast loop
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

A full run is ~4 minutes and three of them are `lib/ir_v1.hthr`. `--no-heavy`
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

**2. Latency budgets** — an absolute ceiling on a corpus file, checked on
every machine, baseline or not. `lib/ir_v1.hthr` is the one that matters:
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
| `kernel` | the `typing::check_type` + `check_term` **gate** that every finished declaration passes (`crates/elab/src/stats.rs`) |
| `elab` | the residue: everything the elaborator did, **including its own conversion and whnf calls into the kernel** |

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
| a fitted slope drifted upward | > +0.35 | as the kernel suite — but the observed run-to-run spread here reached 0.25 on `forded/declared-index-tags`, so a lone slope flag wants a re-run too |
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

## The baseline file

`crates/elab/benches/baseline.tsv`, tab-separated for the kernel suite's
reasons (greppable, diffable, parseable without a dependency). Rows are `env`
(host, cpu, profile, rustc, commit), `case` (family, label, min ns), `split`
(family, label, phase, ns) and `slope`. The key is a **label**, not a size —
corpus cases are named by file.

Re-record when the machine changes, the toolchain changes, or a deliberate
change moves the numbers. A baseline from another machine still gates slopes,
bands and budgets, and `--check` says which half it skipped.

> **The baseline in the tree was re-recorded 2026-08-05** (the code-definition
> round, load ~3–6 — quieter than 2026-08-04's ~10 but not quiet). Absolute
> times still carry a ~1.2–1.5× machine-noise width; the slopes, the phase
> proportions and the budgets are the trustworthy half. Re-record on a quiet
> machine before trusting the time half of `--check`.

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
  rebuild the prelude (~90 µs) or clone a prelude'd one (~108 ns — both
  numbers are in the report, as `corpus/prelude`). The corpus rebuilds,
  because that is what `heather check <file>` does per file and the corpus
  number is meant to be the number a user waits for. Generated families
  clone, because a 90 µs fixed cost against a fixture that starts at ~180 µs
  does not merely add noise to the fit — it *flattens the exponent*, which is
  the number this suite reports.

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

The spread is the point of the noise warning above, and it is also the
argument for the slope being the headline: the times moved by up to 1.5×
between those runs, the exponents by ≤0.25.

Since modules landed (docs/modules-design.md §7), `corpus/check-file` times
an **import closure** rather than a file: `lib/ir_v1.hthr` imports
`lib/std/nat.hthr`, and what `heather check lib/ir_v1.hthr` makes a user wait
for is both. The x-axis stays the root's bytes — the label names the root —
so the two `ir_v1` cases legitimately changed *shape*, not merely time, on
2026-08-05, and their baseline rows have to be re-recorded rather than
compared across that boundary.

No exponent is claimed for the corpus: the x-axis is source bytes across
unrelated files, and `lib/ir_v1.hthr` is not "a bigger `lib/vec_code.hthr`" —
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
~19 ms per use** at an unchanged slope of ~1.0. `lib/ir_v1.hthr` did not
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

`lib/ir_v1.hthr`: parse **0.0%**, elaborate **1.2%**, kernel gate **98.8%**.
`lib/vec_code.hthr`, a file with no deep proofs in it: parse 10.6%, elaborate
49.3%, kernel gate 40.2%.

The issue guessed that a split would tell a regression which layer it was in.
It does — and it also says that on the file that dominates the tree's check
time, the frontend is 1% of the wait. Elaborator optimizations aimed at
`lib/ir_v1.hthr` would be aimed at 1.2% of it; the leverage is entirely in
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
