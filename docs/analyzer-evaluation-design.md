# Running an in-language analyzer: the value-domain readback

Owning issue: `issues/certgen-analyzer-evaluation-cost.md`. Written per the
`docs/nbe-conversion-design.md` / `docs/wf-former-design.md` discipline:
attribution first, then the mechanism, then the rejected alternatives with
their reasons, with the acceptance stated before the first line of code.

The defect in one sentence: `crates/elab/src/certgen.rs`'s `Reader` drove the
kernel's **rewriter** over values whose annotations are `Wf`-lowered
inductives, and a rewriter's cost is *per step, in the size of the term it is
rewriting* — so a readback of two thousand reduction steps took half a minute,
with single steps costing seconds.

The fix is one seam, no kernel rule and no kernel line: the reader is
re-instantiated at the **value domain** the `nbe-conversion` round already
built and shipped for conversion. Values have environments and closures, so a
branch is entered rather than copied, and an annotation nobody inspects is
never traversed at all.

---

## 1. The attribution

The issue named "repeated unshared reduction of `match`es on `Pre` and `TA`"
as what was left after two refuted hypotheses. **The measurement says the
repetition is not there** — and that is the round's finding, because it moves
the fix from a memo table to a different evaluator.

Instrumented on the constructor-fields workload (the acceptance workload of
`docs/certgen-ctor-fields-design.md` §8), debug, one thread, counting every
`Reader::whnf` call and every `reduce::step_term_delta` it spent. Numbers are
in the issue's log; the shapes:

- **The walk is already minimal.** Generating `peek` — one bare constructor
  field, 25 s — is **312 reader steps and about two thousand reduction steps
  in total**, across the transcriber and the certificate fold together. There
  is no repeated sub-spine to memoize: nothing is reduced twice, because the
  reader only ever forces what it is about to look at, exactly as its comment
  claims.
- **The cost is per step, and it is enormous.** Two thousand steps in 25 s is
  ~12 ms per reduction step, and the distribution is worse than the average:
  the single most expensive step in `peek`'s certificate fold is **one
  `ElimWf` step taking 2.1 seconds**. One step.
- **The seam is the whole cost.** Summing the wall time inside `Reader::whnf`
  accounts for ~99% of a fixture's generation time. Nothing else in the
  generator matters.
- **The dominant site is the certificate fold, not the transcriber**, and
  inside it the `Wf` eliminator: for `peek`, 15.6 s of the fold's 22.4 s is
  274 `ElimWf` steps, and the transcriber's whole share is 3.8 s. `mul` — the
  shipped fragment's most expensive fixture — is 16.1 s of fold against 2.6 s
  of transcription.

Why a step costs that: `reduce.rs` is a rewriter. Each `step_term_delta`
descends the congruence rules to find the redex and **rebuilds the path**, and
firing an eliminator instantiates the branch with `apply_local`, which
**copies the branch body**. Both walks carry every type annotation on every
node, and the annotations here are lowered inductives — `Pre`, `Ir`, `Cert` —
whose `Wf` shape and arity slots are the largest terms in the library. So each
step's output is larger than its input and the next step copies more. That is
the term-growth pathology `issues/whnf-sharing-term-growth.md` owns, arriving
at the analyzer seam because this is the one place in the elaborator that runs
a *program* by reduction rather than comparing two terms.

Two further hypotheses were tested here and refuted, so that a later round
does not re-test them:

- **It is not the δ rescope.** Every unfold of a library global rescopes its
  whole body with `shift_global`, and the reader had no `BodyCache`. Wiring
  `Defs::transparent_cached` into the *rewriter* reader moved `peek` from
  25.4 s to 26.7 s — i.e. nothing, inside noise. (The cache is kept in the
  final design anyway: under the evaluator it is free and correct, and it is
  the shape the kernel's own conversion uses.)
- **It is not the reader's traversal.** 312 forces for a 25-second fixture.

This also retires the issue's phrase "cost tracks the payload's STRUCTURE" as
an explanation rather than an observation: structure is what puts a `Wf` value
into an eliminator's scrutinee position, and each such elimination is one
rewrite of a term whose size the structure fixes.

## 2. The mechanism

**Decision: instantiate `Reader` at `heather_kernel::value`, and drive it with
`heather_kernel::eval::Eval`.** The kernel gains nothing — not a rule, not a
former, not a function. `certgen.rs` stops calling `reduce::whnf_term_delta`
and starts calling `Eval::force`.

Concretely, and this is the whole change:

| before | after |
| --- | --- |
| `Reader` holds `&Term`s and returns `Vec<Term>` | it holds `Rc<TmClo>`s and returns `Vec<Rc<TmClo>>` |
| `whnf(&Term) -> Term` | `force(&Rc<TmClo>) -> Rc<Val>` |
| match on `Term::Supf`/`Pair`/`Inl`/`Inr`/`Triv`/`Zero`/`Succ` | match on the `Val` of the same name |
| a field is `(*fst).clone()` — a term clone | a field is `Rc::clone(fst)` — a pointer |
| `run_transcriber` hands the fold an `Ir` **term** | it hands the fold the `Ir` **closure** |
| `global_app` builds an `App` **term** | `global_app1` builds a pending `Elim::App` |

Three properties do the work, all of them the value domain's and none of them
new:

1. **β does not copy.** Entering a branch extends an environment. The
   `ElimWf` step that cost 2.1 seconds allocates one environment cell.
2. **Annotations are never traversed.** A `TyClo` is syntax plus an
   environment; forcing it is what makes it a type, and the reader never
   forces one. The `Wf` shape and arity slots that dominate the terms are
   carried as pointers from beginning to end.
3. **The query shares recent forces** through a bounded cache, written on
   success only. Consumers see the same cached value; FIFO eviction reclaims
   old payloads even though the query arena retains their closure skeletons.
   This is the sharing the issue asked for without whole-query value
   retention, and it is the *smaller* half of the win.

`global_app1` is the one piece of genuinely new code, and it exists to keep
the `Ir` in the value domain end to end: the transcriber's answer must be fed
to `cert_body`, and building an application *term* around it would mean
writing a value back into syntax. Instead the application is a pending
`Elim::App` over the `Ir`'s own closure — the glued-neutral shape of
`docs/nbe-conversion-design.md` §5. The fold therefore inherits the cache the
transcription readback wrote.

**This preserves that document's §7 invariant**, and preserving it is why the
design is stated this way rather than as "normalize once": *no value is ever
converted back into syntax that is then evaluated*. There is still no readback
function in the kernel, and this round does not want one — the reader consumes
values directly into its own `RIr`/`RCert` models, which are `u64`s and
`Vec`s, not terms.

### Where it lives, and the frozen-walker rule

At the rim, in `crates/elab/src/certgen.rs`, which is where the
certifying-generator split says Rust belongs: the *analysis* is in-language
and untouched — `lib/certgen/certgen_code.hthr` and `lib/certgen/certgen_cert.hthr` are
byte-identical across this round — and what changed is only *how the
elaborator runs them*. That is the same category as `analyzer_app`'s spine
construction: invocation, not analysis.

### Fuel

`READ_FUEL` is `DEFAULT_FUEL` (2^20), spent per `force`. The unit changed and
the constant did not, and that is deliberately the tighter choice: under the
rewriter each of the ~300 `whnf` calls got its own 2^20; under the evaluator
each `force` gets 2^20 of the *shared* graph, so a fixture's whole budget is
now what one sub-spine used to get. Measured headroom on the widest fixture in
the acceptance workload: the most expensive single force spends **831** steps
and a whole generation spends **~2050**, against a budget of 1,048,576 — three
orders of magnitude. Running out stays a decline, like every other refusal at
this rim.

## 3. What it costs in memory, and why the discipline holds

CLAUDE.md's memory discipline, and the issue's explicit constraint, is that
whatever replaces the spine-directed walk **must not normalize a whole `Ir`
tree at once**. The design does not, and the reason is structural rather than
a budget:

- `Eval::force` computes a **weak head** value. Its children are closures.
  Nothing under the head is evaluated until the reader asks for it, and the
  reader asks in exactly the order it prints — the same demand order the
  spine-directed walk had. "Normalize once" is *not* what this design does;
  "evaluate once, weak-head, shared" is.
- The live set is therefore the value graph of the part of the answer already
  read, plus its memos. That graph is smaller than the terms the rewriter was
  building, not larger, because its nodes hold pointers to shared syntax where
  the rewriter held copies.
- The trampoline (`Eval::drive`) keeps reduction *steps* off the native stack,
  so a runaway analyzer returns `OutOfFuel` instead of overflowing — strictly
  better than the rewriter, which recursed per congruence level.
- The reader's own `READ_BUDGET` of 4096 instructions is unchanged and still
  bounds the traversal against a library file that may be wrong in any way.

Measured rather than argued: the acceptance workload — elaborating the whole
library prefix and generating all eight fixtures, including the one that
previously did not finish at 16 GiB — peaks at **~54 MiB RSS** and runs to
completion inside `scripts/test`'s own `ulimit -v 4194304`.

## 4. Rejected alternatives

- **A memo table at the analyzer seam, keyed by sub-spine identity** — the
  issue's lever 1 as written. Rejected on the measurement: there is no
  repetition to memoize (§1), so the table would be a pure cost. Had it been
  built first, it would have measured as a no-op and the round would have
  concluded the seam was not the problem — which is why §1 is the first
  section.
- **Normalize-once with bounded depth.** Rejected on the memory discipline it
  is trying to respect: any depth bound large enough to reach the bottom of a
  `Cert` chain normalizes the whole chain, and a bound small enough to be safe
  needs a re-entry mechanism that is just demand-driven forcing with extra
  steps. Weak-head forcing *is* the bounded-depth design, with the bound
  chosen by the consumer.
- **A `BodyCache` on the rewriter alone** — one line, and it is what a cheap
  reading of "no sharing" suggests first. Measured: no movement (§1). Kept
  under the evaluator because it is free there, not because it earned its
  place here.
- **Making the analyzers cheaper in-language** (the issue's lever 2, a
  smaller `TA`: split the `Pre`-carrying payload states out, the `VOut` move
  applied again). Not taken, and the reason is that lever 1 removed the
  constraint entirely — the widest fixture in the acceptance workload
  generates in ~50 ms. Taking lever 2 now would be paying library complexity
  for a cost that is no longer measurable. It stays available and stays
  described on the issue.
- **Moving `typing.rs` to values as well.** Out of scope and unmotivated: the
  nbe design's §7 keeps the rewriter for typing deliberately, and nothing here
  measures typing. This round is one consumer, at one seam.
- **Any kernel change.** None was needed in this round. The value domain, the
  evaluator, the glued neutrals and the body cache were all shipped by the nbe
  round and are all `pub`. At the time the kernel had zero dependencies and
  this round added no rule, so `crates/kernel/DESIGN.md` was untouched.

## 5. Acceptance

Stated before the implementation, met by it:

1. Every existing emission is byte-identical — the generated text is a
   function of the analyzers' answers, and the answers do not change because
   the evaluator agrees with the rewriter. Pinned by the whole certgen family,
   which compares emissions and IR literally.
2. The perturbed-library controls still refuse. A faster evaluator that
   accepted a mutant would be the failure mode worth fearing, and the controls
   are the instrument for it — including the new field-merge control this
   round adds.
3. Per-fixture generation fits `scripts/test`'s debug rails with headroom,
   including the two-field-one-computed constructor that previously did not
   finish.
4. `scripts/bench --check` clean: the kernel is untouched, so any movement
   would be a mistake.
