# How principled is the elaborator? A survey and a consolidation plan

Prompted by PR #387 (`issues/index-inference-through-unfolding.md`): the
unifier's rigid-spine alignment set `?≈ := Rat::Same` although `?≈`'s type
`Int → Int → Type` was already fixed, and the fix added a post-hoc type check
plus an 8-step unfolding fallback. Minus asked whether such fixes point at
missing general rules, and whether the elaborator should consolidate into a
smaller set of simple principles. This note answers from the code on master
(`786b5eb`), the issue tracker, and the recursion cluster of 2026-11-02
(#383, #389, `recursion-let-reads-changing-parameter`,
`recursion-case-split-dependent-ih`, `decreases-shadowed-let`).

It is an analysis. It proposes, and files issues; it changes no code.

## 0. Summary

The elaborator has one sound, well-kept invariant, and it carries more weight
than it can bear. The invariant: **every guess is learn-only, and the kernel
re-checks the result** (`docs/elaborator/unifier-completeness-design.md` §1). That makes
a wrong guess harmless for *soundness*. It does not make it harmless for
*completeness* or for *meaning*:

- A wrong unifier guess is **sticky** (only `Unsolved` slots are ever
  written, and a later disagreeing occurrence is never compared), so it
  blocks the right solution and sends instance search down a hopeless path.
  The user gets a refusal of a correct program, with a message about a type
  nobody wrote. Each such bug has been fixed by a guard that forbids one
  shape of guess. That is how `unify_tm` got its twelve issue-citing rules.
- A wrong *recursion compilation* is a well-typed term that means a
  different function. The kernel accepts it, and `refl` proves the wrong
  equation. The kernel can only catch what is ill-typed, and these are not.

Five clusters of bugs share a single cause: a fast syntactic approximation of
a semantic question (conversion, scoping, meaning) whose answer is trusted
beyond what it can justify, plus a guard per observed failure. The proposal
is five principles, each of which replaces a family of guards:

| | Principle | Replaces |
|---|---|---|
| P1 | **A meta is written in one place, and that place checks the solution** (type, scope, agreement with what is already known) | `reject_ill_typed_solutions`, the two post-hoc call sites, silent first-write-wins |
| P2 | **Forced solutions before guesses**; an approximation is a ranked, postponed guess, never a congruence step | the distinct-heads, spine-length and flex-head guards; `applied-meta-approximation-diagnostics` |
| P3 | **Rigid–rigid mismatch means lazy δ**: the unifier and every matcher follow the kernel's δ-lazy conversion order when two rigid heads differ (unfold, compare again), instead of bounded walks | the "learned nothing → whnf" retries, `INDEX_UNFOLD_STEPS`, 17 bounded `term_reducts` walks with seven different budgets |
| P4 | **A compiled definition is checked against its source**: the unfolding equation of every recursive definition is generated and kernel-checked, so a miscompile is a refusal | today nothing: the miscompile class is silent |
| P5 | **Analyses run on binder identities, not names** | the recursion planner's name-keyed scope, measure lifting's shadow handling, `select_scope` declining |

Recommended order (§8): P4 first (it is the only class the kernel cannot
catch), then P1 (small, absorbs #387), then the P3 primitive as a
behaviour-preserving refactor, then P3's lazy δ in the unifier, then P2, and
P5 together with the longer-term recursion lowering of §6.3.

## 1. What is already principled

Worth saying first, because the proposals keep all of it.

- **The kernel is the gate.** Nothing the elaborator guesses is trusted for
  soundness. Every bug in this survey is a refusal of a good program, a bad
  message, or (§6) a wrong meaning, never an unsound acceptance.
- **The slot model is honest.** `Sol::{Unsolved, Withheld, Solved}`
  (`crates/elab/src/unification.rs:84`) replaced a placeholder hack, and
  `zonked` decides readiness exactly. Deferral is per call with no
  cross-call queue, by a stated decision (§3.1 of the unifier design).
- **Instance search has an ordered, documented source list** with a
  machine-readable trace (`crates/elab/src/resolve.rs`: canonical table,
  scope, upcast, registry, merged-class join, computation, evidence rules,
  unfold-to-ruled). The order is a policy you can read.
- **Most special cases cite their issue.** That is what made this survey
  possible: the guards are documented one by one. The problem is their
  number, not their opacity.

## 2. The bug record

Counted over `issues/*.md` titles (1300 issues, 775 closed); keyword buckets
overlap and are a shape, not a census.

| Cluster | Open | Closed | Representative issues |
|---|---|---|---|
| Inference/implicit/unifier | 20 | 39 | `index-inference-through-unfolding`, `unifier-spine-across-distinct-heads`, `constrained-predicate-expected-type`, `and-at-match-predicate-implicit-level-mismatch`, `applied-meta-approximation-diagnostics`, `argument-type-reduction-after-partial-inference` |
| Unfolding/reduction gaps | 17 | 31 | `unify-succ-under-addition`, `exists-proof-projection-type-not-reduced`, `motive-application-hides-hypothesis-type`, `decide-at-defined-proposition`, `grind-definitional-equalities` |
| Spelling | 14 | 31 | `elaborator-canonical-type-spelling` and the respell family |
| Recursion/guard/decreases | 25 | 50 | `recursive-arm-reads-outer-scrutinee`, `recursion-let-reads-changing-parameter`, `recursion-branch-on-varied-parameter` (#389), `recursion-guard-takes-nearest-parameter-match`, `recursion-outer-match-takes-guard-without-descent`, `recursion-case-split-dependent-ih`, `decreases-shadowed-let` |
| "Elaborator accepts, kernel refuses" | — | ≥7 | `eqbind-deep-pattern-kernel-rejects`, `indexed-deep-pattern-kernel-rejects`, `wf-nested-match-motive-synthesis-kernel-refusal`, `prop-in-bool-position-reaches-kernel`, `generic-congruence-inferred-type-arg-level-mismatch`, `omega-shadowed-binder-certificate` |
| Silent wrong meaning | — | ≥4 | `recursive-arm-reads-outer-scrutinee`, `recursion-let-reads-changing-parameter`, `recursion-branch-on-varied-parameter`, `deep-pattern-ctor-needs-column-type` |

Two patterns stand out in the fixes.

1. **A fix forbids one shape, and the next bug is the neighbouring shape.**
   Spines of different lengths (`constrained-predicate-expected-type`,
   2026-10-19) → different heads at the same length
   (`and-at-match-predicate…`, 2026-10-30) → a *meta* head against a rigid
   head of the wrong type (#387, 2026-11-02). In recursion: the parameter read
   inside its arm (2026-09-25) → a `let` above the match reading a varied
   parameter → a *branch* above the match reading a varied parameter (#389)
   → nearest vs outermost guard (#383, #389). Each is the same question asked
   about one more syntactic form.
2. **Retries are triggered by a proxy, not by the failure.** `unify_arg_ty`
   reduces the argument type only if the first read "learned nothing"; #387
   added "or a solution was rejected"; `argument-type-reduction-after-partial-
   inference` asks for "or partial progress, but not always". The real
   trigger is local and structural: *two rigid heads disagreed here*.

## 3. The unifier (`crates/elab/src/unification.rs`)

### 3.1 What it is

`unify_tm` is a syntactic congruence over every kernel former, learn-only: a
meta at the identity substitution meeting any subject takes the subject
(`unification.rs:580`), every other pair recurses or does nothing. Over this
sit:

- five semantic callbacks on `U` (`type_args`, `canonical_head`, `respell`,
  `constructor`, `slot_view`), each a view the syntactic rule could not
  produce;
- guards inside the `App` case: flex head over a λ solution, declared slot,
  matching value spine, different spine lengths, distinct heads;
- the canonical-head rule (reduce a global-headed subject when the pattern
  is a constructor form);
- around it, at its two main callers (`unify_arg_ty`, `solve_from_expected`
  in `crates/elab/src/lib.rs`): inline/unspell, read, check the solutions'
  types (#387), walk 8 reducts, whnf, read again.

Twelve distinct issues are cited from inside `unification.rs` alone.

### 3.2 What is missing, stated as rules

**No checked assignment.** The write is `sols[i] = Sol::Solved(s)` at one
line, with a scope check (`subject_tm` strengthens) but no type check. #387
added the type check *after* whole reads, at two call sites, and only for
Π-typed slots, by snapshotting `Unsolved` marks and undoing. Every other
caller of `unify_root` (`host.rs` ×3, `application/polymorphic.rs`) is still
unchecked. The principled form is the textbook one: `assign(i, s)` checks
scope, occurs, and that `s`'s type converts with slot `i`'s (zonked) type,
and refuses the write otherwise. That is P1.

**First write wins, silently.** If `?a` is already solved, the meta arm
returns without comparing. `f(?a, ?a)` against `f(x, y)` learns `?a := x` and
says nothing about `y`. In a Lean-style unifier the solved meta is
instantiated and the comparison continues; a disagreement is a *signal*
(retry with δ, or report the conflict at the right place). P1 includes this:
a solved meta's occurrence compares its solution against the subject,
learn-only (it never fails the call), but a disagreement is recorded, and is
exactly the trigger P3 wants.

**Guesses are mixed into congruence.** Three rules are not consequences of
the equation but approximations: peeling a rigid spine for an applied meta
(`?op(x, y)` learns `append<A>`), the last-argument abstraction for
`?M(A) ≟ F<B, A>` (`applied-meta-approximation-diagnostics`), and positional
pairing of two rigid spines (now fenced by the length and head guards). In
higher-order unification practice (Lean 4's `isDefEq`, Agda, Abel–Pientka's
dynamic pattern unification) the order is: decided rules (pattern fragment,
same rigid head) first, δ on head mismatch, and approximations last, as a
postponed choice. P2 makes that order explicit. The distinct-heads and
spine-length guards then stop being guards: two distinct rigid heads are
never paired positionally at all, because positional pairing is only ever
done for *the same* head, and different heads go to P3.

**Head mismatch has no rule.** Today two different rigid heads learn
nothing (after the 2026-10-30 guard), and a caller may later whnf the whole
type. The decided rule in every mature checker is lazy δ: unfold the side
whose definition is "higher" (defined later, in terms of the other), one
step, and compare again (Lean 4 `lazyDeltaReduction`, Coq's
`Conversion` oracle). Heather's own kernel already converts in a δ-lazy
order (`crates/kernel/DESIGN.md`, "Conversion is δ-lazy": same head →
compare spines; otherwise unfold to δ-heads and compare again). The
unifier is, in effect, learn-only conversion with metas, and it does not
follow its own kernel's order. The simplest form of P3 is therefore **the
unifier mirrors the kernel's conversion order**, with solutions recorded
where conversion would compare a meta. Definitional heights (one plus the
maximum over the globals a body mentions, computed at declaration and kept
in the module image) are a refinement for both: they pick which side to
unfold instead of unfolding both. P3 is what #387's "read up to 8 reducts,
global-headed only" is approximating.

### 3.3 What P1–P3 would have done with the recent bugs

| Bug | Under P1–P3 |
|---|---|
| #387 `?≈ := Rat::Same` at `Int → Int → Type` | P1 refuses the write at the assignment; the δ walk is P3's: `Rat::Same(x,y)` is higher than `Int` operations, unfolds once, and meets `?≈(?*(…),?*(…))` |
| `unifier-spine-across-distinct-heads` (`and(?a,?b)` vs `g(n,m)`) | distinct heads → P3 unfolds `g`, `pick(h)` elaborates (the issue's second reading) |
| `constrained-predicate-expected-type` (different spine lengths) | never paired positionally (P2); P3 unfolds the higher side |
| `argument-type-reduction-after-partial-inference` | the mismatch at `lookup(…)` vs `Some(?left)` is P3's local trigger; no global "learned nothing" proxy |
| `decide-at-defined-proposition` (instance head `?P ∧ ?Q` vs `Canonical(…)`) | P3 in instance-head matching (§4): `Canonical` unfolds |
| `applied-meta-approximation-diagnostics` | the last-argument guess is a ranked guess (P2) and its diagnostic names the guess |

## 4. Instance search and the other matchers

There are at least five matchers with five policies:

| Matcher | Where | Repeated binder | Head mismatch | Typed? |
|---|---|---|---|---|
| `unify_tm` | `unification.rs` | first write wins, unchecked | nothing (caller may whnf) | #387 post hoc, Π slots only |
| rewrite's `match_spine` | `rewrite.rs:499` | compared by conversion | — | instance re-checked by conversion |
| host `match_at` | `host.rs:2812` | via `unify_root` | via callers | — |
| LGG | `lgg.rs` | by construction | — | — |
| instance candidates | `resolve.rs:923` | n/a: the candidate is *fully elaborated* at the goal, then `checks_at` converts | δ only through `unfolded_to_ruled` (64 steps, propositions only) | yes, by the kernel, after building |

Instance search builds every candidate (`build_candidate` → `elab_check`)
and only then asks whether it is of the goal type. That is the route by
which #387 surfaced ("built, but not of the goal type" ×N), it is the
fan-out `resolution-candidate-fan-out` measures, and it is why a failing
`mono` search costs gigabytes (`mono-failure-under-upcast-cost`). The
consolidated form is the standard one: match the instance's *conclusion*
against the goal with the same unifier (P1–P3 included) before elaborating
the candidate's premises; a discrimination index over conclusions is the
later optimisation. `rewrite`'s matcher and `host::match_at` become the same
unifier at a different transparency, not separate code.

This is the "one matcher" consolidation. It is filed as one issue
(§9), sequenced after P1–P3 because it should reuse them rather than copy
them.

## 5. Budgets and bounded walks

`grep term_reducts` finds **17 call sites** of one pattern: walk up to *N*
reducts of a term and take the first whose head satisfies a predicate. The
budgets are 1, 4, 8, 8, 16, 16, 16, 32, 32, 64 (×5), 1024 (×2):

`omega_cert.rs` (×3, `PROPOSITION_UNFOLD_STEPS` and a bare 64), `resolve.rs`
(`UNFOLD_STEPS`), `ring.rs` (`WRAPPER_STEPS`), `host.rs`
(`HOLE_UNFOLD_STEPS`), `goal_combinators.rs` (8, 64, 64, 16), `lib.rs`
(32, `INDEX_UNFOLD_STEPS`), `bv_omega.rs` (`UNFOLD_STEPS`),
`relational_context/proof.rs` (1, 1), `literals.rs` (32), `iwf_family.rs`
and `indexed.rs` (1024).

Each budget was tuned to its first customer. A step count is the wrong unit:
a single δ step on a large definition and a single β step cost very
different amounts, and "8" for #387 is "a δ and the β steps that apply the
body, twice over", i.e. it is counting *definitions*, not steps. What every
site wants is **"the nearest unfolding of `t` whose head satisfies `P`, at
transparency `τ`"**. With definitional heights, "unfold the highest head one
δ step, then β/ι to weak head" terminates without a count for non-recursive
definitions, and the count that remains is a single fuel policy for genuine
computation (recursors on literals), shared with the oracle.

Concretely: one primitive `unfold_to(t, τ, P)` in `oracle.rs`, every site
calling it with its predicate, first with each site's current budget so the
refactor changes no counter (`scripts/timings --diff` with identical count
columns proves it), then heights replace the budgets one site at a time.
`STUCK_SPELLING_STEPS`, the display budgets and the kernel's own fuel are
out of scope: they bound *output* or *trusted* work, which is a different
question.

## 6. Recursion compilation: the one class the kernel cannot catch

### 6.1 Why this cluster is different

`crates/elab/src/recursion.rs` compiles structural recursion **at a surface
`match`**: the recursor is placed at the match the planner chooses, the
self-call becomes the eliminator's hypothesis, and "everything outside the
`match` is evaluated once, by the top call" (`RecursionPlan`'s doc comment,
`recursion.rs:290`). That is the function only if nothing between the
function's entry and the match depends on a parameter the self-calls vary.
The planner therefore re-derives, on the surface syntax, which names depend
on which parameters, and refuses or re-routes (`ByMeasure`, `Misplaced`)
when the condition fails.

When the planner misses a form, the result is a well-typed term with a
different meaning. `recursion-let-reads-changing-parameter`: `u(1, x) = x +
1` checked by `refl` where the source says `x + 11`. #389: `v2(1, [3, 0, 4])`
compiled to 7, the source says 0. These are exactly as dangerous as an
unsound kernel for anyone relying on a definition's behaviour, and the
kernel is no help: the compiled term is the definition.

### 6.2 The planner is a second scoping semantics

`plan`/`reads`/`bind_statement` walk the surface with a name-keyed scope
(`Bound { name: String, … }`, `lookup` by string equality). Its coverage is
whatever forms it lists; everything else falls through to
`surface::for_each_child`, which does not bind. By reading (not yet probed):
`Stmt::LetCode` binds a name that `bind_statement` does not record, and
`ExprKind::MatchCode`'s arm binders fall through unbound, so a shadowing
binder in either is read as the outer name. Every new binding form
(`for`, `let mut`, binding statements, landed 2026-11-01/02) has to be added
here as well as in the elaborator, or it silently drifts. That is the
structural reason the cluster keeps growing, and the same shape as
`decreases-shadowed-let` (measure lifting reads names; the workaround is
SSA renaming in `alpha.rs`).

### 6.3 Principles

**P4, the safety net: check the meaning.** For every structurally recursive
definition, generate its unfolding equation per constructor of the
decreasing parameter, `f(C(ȳ), x̄) = body[f][n := C(ȳ)]`, and have the kernel
check it by conversion, as the gate does any `refl`. For a correct
compilation both sides should reduce to the same arm with the same recursive calls
(the self-call is `F(k, …)` on both sides). For the stale-`let`, the
varied-branch and the outer-scrutinee bugs the two sides differ at an open
argument and conversion refuses, so the miscompile becomes a located
refusal at declaration. The `decreases` lowering already generates
`f_unfold` with a proof (`docs/language/recursion/decreases-unfolding-design.md`); structural
recursion needs no proof, only conversion.

Cost: one conversion per constructor per recursive definition, about the size
of the body unfolded once on each side. Risk: false refusals where the
compilation is right but conversion cannot see it (convoys, course-of-values
windows, dependent ihs). Mitigation: land it first as a mode that *reports*
over the whole library (`heather check --check-meaning` or a gate flag), read
the false-refusal list, and turn it into a refusal once that list is empty
or each entry is an issue. It also gives every structural `fn` an
`f_unfold`-style equation clients could cite, which `fn-recursion-means-the-
function` and the proof guide would use.

**P5: analyses on binder identities.** The planner and measure lifting run
after one uniform renaming pass (the `alpha.rs` renamer, generalised to all
binding forms) so that a name *is* its binder, or better, on the elaborated
term, where binders are de Bruijn positions and the scoping is the
elaborator's own. `guard-matches-self-calls-by-term` is the same lesson from
the `Wf` side.

**Longer term: put the recursion at the top.** Lean's structural recursion
compiles the *whole body* against `brecOn` on the decreasing argument, with
every other parameter generalised in the motive; self-calls become
projections from the `below` structure. Under that lowering the position of
the `match` is irrelevant, everything the body computes is recomputed at
each level, and the guard-selection family (nearest, outermost, case split,
dependent ih, varied branch, stale `let`, course of values at depth *d*)
stops being questions. Heather already has course-of-values on `Nat`
(`docs/language/recursion/course-of-values-recursion-design.md`), which is the `below` for one
inductive; the general one needs a `below` per lowered inductive (W/Wf
tiers), which is real work and a design round of its own. P4 is worth doing
regardless, because it checks whichever lowering is in place.

## 7. Spelling, briefly

`unspell`/`respell` appear about 425 times in `crates/elab/src`. The unifier
needs `respell`, `constructor`, `slot_view` and an `unspell_deep_now` on both
sides of every read because a type has two spellings (the inline lowering and
the registered code reference). This is the territory of the existing open
issues `elaborator-canonical-type-spelling` and `elaborator-glued-evaluation`
(fundamental-improvements item 1), and this note does not re-propose them.
Two remarks only: P3's lazy δ is the operation that makes two spellings meet
without a respelling table (the code reference is higher than its inline
lowering, so it unfolds to it), and glued evaluation would let P3 run on
values with the folded form kept for solutions and display. P3 does not wait
for either.

## 8. Order of work, costs and risks

1. **P4 meaning check, report mode, then refusal** (`recursion-meaning-check`).
   Highest value per cost: it is the only class of bug that reaches users as
   a wrong answer. Cost: one conversion per constructor per recursive
   definition at the gate. Risk: false refusals; report mode first. No
   unifier change. *Status (2026-11-06):* a refusal at the declaration for
   "does not unfold"; an unsettled check refuses nothing (`meaning.rs`).
2. **P1 checked assignment** (`unifier-checked-assignment`). Small: one
   `assign` used by every write, with #387's check moved inside it and
   generalised to every slot whose type is meta-free, plus agreement
   comparison for already-solved metas. Cost: a kernel `infer` + `convert`
   per solution on the hottest path in the elaborator. That is a new
   inference route on a hot path, so per CLAUDE.md this round measures with
   `scripts/perf ab`. Mitigations if needed: compare heads first (a global's
   type is a lookup), skip slots whose type is a sort. Risk: low. A wrong-typed solution
   can never have been corrected later (first write wins), so every call
   that elaborates today keeps its solutions; the expected changes are
   refusals that move earlier with better messages, and calls like #387's
   that now find the right solution.
3. **`unfold_to` primitive** (`one-unfold-to-primitive`). A refactor of the 17
   sites with their current budgets, identical counters. Low risk, and it is
   the seam for step 4.
4. **Lazy δ at rigid–rigid mismatch** (P3, `unifier-lazy-delta`). The
   unifier's distinct-head case follows the kernel's δ-lazy order (unfold
   to δ-heads, compare again; definitional heights later pick one side); the "learned nothing → whnf"
   retries and `INDEX_UNFOLD_STEPS` are deleted when the library passes
   without them. Cost: unfolding in the unifier is what "elaborator whnf is
   the cost" warns about, so it must be one δ step at a time and only at a
   mismatch, and the round measures. Risk: different (more) solutions found,
   so some library calls elaborate differently; interface definitions
   (`interface fn`, withheld) must stay opaque, which a transparency
   parameter gives for free.
5. **P2 guesses ranked after forced solutions** (`unifier-guesses-postponed`).
   The applied-meta approximation and value-spine peeling move out of the
   congruence into a final, named step; diagnostics name the guess. After 4,
   because P3 removes most of the need for positional pairing of distinct
   heads.
6. **One matcher for instance heads, rewrite and host matching**
   (`instance-conclusion-matched-first`). After 1–5 so it reuses them.
7. **P5 and the top-level recursion lowering** (`recursion-on-elaborated-terms`).
   A design round; P4 keeps the current lowering honest meanwhile. The
   options are in docs/language/recursion/recursion-at-the-top-design.md.

What this does **not** propose: a constraint store with cross-call
postponement (the unifier design declined it for good reasons, and nothing
here needs it); higher-order pattern inversion beyond the identity renaming
(`elab-unifier-completeness` §6 owns it); changes to the kernel.

## 9. Issues filed

- `recursion-meaning-check` (P4)
- `unifier-checked-assignment` (P1)
- `one-unfold-to-primitive` (P3, refactor)
- `unifier-lazy-delta` (P3)
- `unifier-guesses-postponed` (P2)
- `instance-conclusion-matched-first` (§4)
- `recursion-on-elaborated-terms` (P5 and §6.3's lowering), whose design
  note (docs/language/recursion/recursion-at-the-top-design.md) filed
  `recursion-below-nat-fallback` (slice 1 of option A, chosen 2026-11-04) and
  `meta-fn-mismatch-reaches-kernel` (found probing)
- `rewrite-matcher-on-unifier` (§4's remainder, filed 2026-11-03 when
  instance search moved onto the unifier; the host's `match_at` already had)
