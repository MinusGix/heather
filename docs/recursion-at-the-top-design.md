# Recursion at the top: compiling structural recursion against `below`

Status: **decided** (Minus, 2026-11-04): option A, staged as §4 lists;
slices 1–3 built (§4, §5); slice 1 is issues/recursion-below-nat-fallback.md
(issues/recursion-on-elaborated-terms.md). Step 7 of
docs/elaborator-principles-survey.md §8, extending its §6.2–6.3.

## 1. The question

Structural recursion is the one class of elaborator bug the kernel cannot
catch (survey §6.1): a miscompiled recursion is a *well-typed* term that
means something else. The planner (`recursion::plan`, `guard_param`,
`outer_case_split`, `descends_through`) decides, on the surface and with a
name-keyed scope (`Bound { name, … }`), which `match` is the recursion, and
compiles the eliminator **at that match**. Everything outside it is computed
once, at the top call. Four families of rules follow from that one choice:

- **Guard selection.** Which `match` takes the guard: nearest
  (recursion-guard-takes-nearest-parameter-match, closed), outermost without
  descent (recursion-outer-match-takes-guard-without-descent, closed), a case
  split whose ih mentions the split parameter
  (recursion-case-split-dependent-ih, open), #389's varied branch.
- **What the arm may read.** The decreasing parameter, or a `let` or `have`
  bound from it above the match, would be the *first* call's value, so it is
  refused (fn-recursion-means-the-function, open). Probe, master c345c863:

  ```
  fn fine(n: Nat) → Nat {
      match n { Zero => 0, Succ(k) => { let j = n; Succ(fine(k)) } }
  }
  // error: `n` is read inside its own recursive `match`: … it would be the
  //        value `fine` was first called with, not this level's.
  ```

  `j` is never used and the function is plainly structural.
- **Which other parameters vary.** ih generalisation scans the surface for
  varied arguments (docs/ih-generalization-design.md), and misses a call
  under `∃` (ih-generalization-under-exists, open).
- **Course of values.** A window of the last *d* values as a Σ tuple over
  `pred^i z` (docs/course-of-values-recursion-design.md,
  docs/list-course-of-values-design.md), with convoys at each nested match:
  cov-window-in-theorem-arms, cov-convoy-motive-second-ambient,
  cov-window-term-size (open), and the Wf arms compared by term
  (guard-matches-self-calls-by-term, open).

Each rule is a patch on the consequences of compiling at the match.
recursion-meaning-check (`crates/elab/src/meaning.rs`; review mode at the
time, a refusal at the declaration since 2026-11-06) now tells us when a
patch is wrong; it does not remove the rules.

## 2. The shadowing readings (the issue's probes)

The issue suspected two drifts of the name-keyed planner: a `let code`
binder and a `match code` arm binder, both unrecorded by `bind_statement`,
read as the outer name. Probed on master c345c863, **neither is reachable**:

- A `meta fn` cannot call itself (`unbound name`), so no `match code` arm is
  ever under a recursion the planner compiles.
- `Code`/`Ctx`/`TyCode` are refused outside a `meta fn` signature, so an
  ordinary recursive `fn` cannot hold either form.
- `let code` in a nested block of a `meta fn` (a `match` arm) is refused as
  meta-layer syntax; only the body's top statements alias.

Both are now expect-error probes in
`lib/_tests/std/core/recursion_binder_tests.hthr`, with the `fine` refusal
above, so a slice that makes meta fns recursive or lets `let code` nest meets
them. The scoping semantics is still a second one: it is right today because
the forms it does not know cannot reach it, which is luck, not a rule.

While probing, a separate gap: any type mismatch inside a `meta fn` (a
`Nat` returned at `Code(g |- Nat)`, or a `match code … as Nat` result there)
is accepted by the elaborator and refused only by the kernel, as a bare
`NotConvertible` at the declaration. Routing the meta gate through
`kernel_refusal` is not enough: its recorded-site matching attributes the
refusal to an earlier declaration's site. Filed as
issues/meta-fn-mismatch-reaches-kernel.md; not part of this design.

## 3. Lowering against `below`

Lean's structural recursion, adapted. For `f(x̄, z, ȳ) → R` recursing on
`z : D`:

1. **`Below`**, by a large elimination of `D` into `Type` (codes: a
   `fn … → Type` already returns them): for `Nat`,
   `Below_M(0) = Unit`, `Below_M(Succ k) = Σ(M(k), Below_M(k))`; for a tier-1
   `Wf` inductive, a Σ over each recursive field of `M(field) × Below(field)`.
   One generic definition per lowered tier, not per function.
2. **The motive generalises every other parameter**:
   `M(z) = Π x̄ ȳ. R`. Nothing is "passed unchanged" or "varied" any more:
   every self-call picks its own `x̄ ȳ`.
3. **`F(z) : Σ(M(z), Below_M(z))`** by the eliminator; `f(x̄, z, ȳ) =
   F(z).1(x̄, ȳ)`. The **whole body** is the step, elaborated with a map from
   each structural subterm of `z` to its `below` accessor.
4. **Self-calls are projections.** Elaborating `f(ā, t, b̄)`: if `t`
   *elaborates to* a key of the map (a de Bruijn variable an arm bound), the
   call is that accessor's `.1(ā, b̄)`; otherwise it is refused as not
   descending. A `match` on a mapped subterm convoys that subterm's `below`
   piece and maps its arm binders one level deeper. Course of values at any
   depth is the same rule applied again.
5. **The decreasing parameter** is the first candidate (the planner's
   surface guess first, then each other inductive parameter) for which every
   self-call is found.

What it buys, rule by rule:

| Today's rule | Under `below` |
|---|---|
| Which `match` is the guard | No guard: matches are ordinary |
| Parameter read in its arm | It is this level's value (the body recomputes) |
| `let`/`have` above the match | Recomputed at each level |
| Varied / dependent ih | Every other parameter is in the motive |
| Window of depth *d* | Accessor chain, types on variables, O(d) |
| Wf arms compared by term | Keys are binder positions |

Unfolding holds **by conversion**: `F(C(ȳ)) ≡ step(C(ȳ), below(C(ȳ)))` and
the accessors reduce to `F(y).1`, which is `f` at `y`. So the meaning check
(P4) passes by construction, and `f#meaning` can become an equation clients
cite. Matching on the elaborated term is P5 for free: the map's keys are
binders, and no name lookup is involved.

What stays as it is: indexed families and IWf (their `below` needs the
index in the motive; later), mutual recursion (`mutual_rec.rs`),
`decreases` (measure lifting already runs over `alpha::deshadow`, #393),
codata (corecursion is a different lowering), and `meta fn`s.

### Costs and risks

- **Term size.** Each level builds a pair; accessors are projections.
  Linear in what the window is quadratic in, but every recursive function's
  term changes, so the default flip is measured (`scripts/perf ab` over the
  library) before it lands.
- **Evaluation.** Closed `refl` verdicts evaluate `F(n)`; the `below`
  component is the eliminator's own recursive argument, so the sharing story
  is the one the current lowering has. A pathological double read of one
  accessor is the thing to watch.
- **Folding back.** Goals that whnf through `f` show the accessor where the
  current lowering shows the eliminator's ih. The display's fold to `f(k)`
  and the `f_unfold` equations must keep working; that is slice 1's test
  value, alongside the meaning check.
- **Elaborating more than once** when the first candidate fails. Bounded by
  the number of inductive parameters, and the surface guess is right
  nearly always.

## 4. Options

**A. `below` at the top, staged (recommended).**
1. *Nat, as the fallback.* Where today's planner refuses a `Nat` recursion
   (the arm reads its parameter, a dependent ih, a let above the match), lower
   by `below` instead. Nothing accepted today changes term. Retires the
   refusals of fn-recursion-means-the-function and
   recursion-case-split-dependent-ih for `Nat`.

   *As built* (§5): `below` is the existing Nat guard's ih and its
   course-of-values window, which the body's nested matches convoy, so no
   new definition was needed and calls at any depth are reached.
2. *Nat, the default.* After `perf ab`, every `Nat` structural recursion
   lowers at the top; delete the Nat guard selection (`guard_param`,
   `outer_case_split`, the planner's Nat routing). The window stays, as the
   `below` it is (§5); cov-window-term-size's Nat half becomes a question
   about that one representation.

   *As built* (2026-11-04, issues/recursion-at-top-nat-default.md): every
   `fn` whose first `match` on a parameter takes apart an explicit `Nat`
   that a self-call descends through lowers at the top first. A first
   attempt generalized every other parameter, as step 2 of §3 says, and
   lost the kernel's run folds (`eval/runs.rs`): `add(m, n)`'s step became
   a fold over functions, opaque to the classifier, and closed arithmetic
   ran out of fuel. So the default generalizes what the calls vary, as the
   plain lowering does, and only a fallback generalizes everything. An
   outer case split (the first parameter `match` with no descent) keeps
   the plain lowering, since moving it inside changes what reduces at an
   open argument. The guard selection stays: nested recursion under the
   top, case splits and the other tiers still use it.

3. *Tier-1 `Wf`.* The generic `Below` for chain-shaped and branching `Wf`
   inductives; delete the Wf window and the term comparison. Retires
   cov-window-in-theorem-arms, cov-convoy-motive-second-ambient,
   guard-matches-self-calls-by-term, ih-generalization-under-exists, the rest
   of cov-window-term-size.

   *As built* (2026-11-07, issues/recursion-at-top-wf.md): by **hoisting**,
   not a new `Below`. The body's own first `match z` moves to the top: one
   arm per constructor, binding that `match`'s own binder names, rebinding
   `z` to the constructor term (`let z: T = Cons(h, t)`), with every
   `match z` in the body replaced by its arm for that constructor (a
   `match` on a known constructor, taken at the surface;
   `recursion_at_top_hoisted` in crates/elab/src/lib.rs). The wrapper is the
   guard (`top_guard` in `elab_match_wf`); everything else is the existing
   tier-1 lowering, so the window is the `below` and its convoys carry calls
   at any depth, as at `Nat` (§5). A body whose `match` is already outermost
   lowers to the same term as before, so the default costs nothing there.
   The rewrite declines (the plain lowering stands) where it would have to
   track scopes: `z` rebound in the body, a `match z` with an equation, a
   written motive or a nested pattern. Hoisted names the rest of the body
   mentions are replaced by fresh ones.

   Retired: ih-generalization-under-exists (summation's `RecSum` is written
   directly), the `fn-recursion-means-the-function` refusals at tier-1 `Wf` (the parameter
   in its arm, a `let` above, a `match` off the result), and the
   branch-on-varied-parameter refusals over a list. **Not** retired: the
   window and the term comparison stay (the keys are still the child terms,
   built by the same alias code at both sites), so
   guard-matches-self-calls-by-term, cov-convoy-motive-second-ambient and
   cov-window-term-size are unchanged, and cov-window-in-theorem-arms'
   second probe (a chain `match` under a `λ`) still gets the outer goal,
   at the top as on master.

   *Follow-up* (2026-11-08): the convoy, which slice 3 keeps as the
   `below`'s carrier, had two defects of its own, both now fixed. It
   reindexed the motive past the binders since the guard instead of since
   the recursion's `match`, so a motive mentioning a type parameter or a
   parameter before the decreasing one was refused by the kernel at depth 2,
   on `Nat` and `List` (cov-convoy-motive-second-ambient, closed). And at a
   `List` it checked a chain `match` under a `λ` against the motive with
   that `λ`'s `Π` still on (cov-window-in-theorem-arms, closed): the
   consumed binders now travel with the window (`WfCov::peel`), chosen by
   conversion against the `match`'s goal only where binders intervene.
   Probes: `lib/_tests/std/core/recursion_window_tests.hthr`.

Retires, at the end: the guard-selection family, the window, the
surface-scoped planner for every inductive below the indexed tier.

**B. Binder identities only.** Run today's planner over `alpha::deshadow`'s
output (or the elaborated arms), keep compiling at the match. Cheap, one
round. Retires the scoping drift, which §2 found unreachable, and nothing in
§1's table. The guard rules stay.

**C. Keep patching.** Fix the open issues one by one under the meaning
check. Each is a small round; the rule count grows.

A is the survey's principle stated as a lowering: the recursion is one rule
(the eliminator at the top) and everything else is ordinary elaboration. Its
first slice changes nothing that is accepted today, so it can land and be
reverted without touching the library.

## 5. Slice 1 as built

`recursion_at_top_body` (crates/elab/src/lib.rs) wraps the body in one
`match` on the parameter at the top, each arm rebinding the parameter's name
to the arm's constructor term (`let z = Succ(z#pred);`). Under
`DynamicScope::recursion_at_top`:

- that `match` is the guard (`top_guard`), whatever `guard_param` would
  say, and every other explicit value parameter is generalized
  (`top_positions`);
- a `Nat` `match` whose scrutinee is a constructor term takes its arm, the
  `Succ(k)` binder an alias of the term (routes.rs), so the body's own
  `match z` binds `k` to the guard's predecessor and a self-call at `k` is
  the ih, compared by binder position as every Nat guard is.

The ih is the eliminator's own, with the course-of-values window of today's
lowering (docs/course-of-values-recursion-design.md) as the `below`: its
depth is read from the chain of nested matches starting at the parameter
itself (`cov_depth` seeded there, one level up), and the body's `match` on
the predecessor convoys it exactly as it does below an ordinary arm, so a
call *d* below the parameter is the window's *d*-th component. Implicit
parameters stay fixed.

It runs where the plan was `ByMeasure`, before the measure (which now
lowers only what does not elaborate at the top), and where elaboration refused a
self-call or the plan's `Misplaced` refusal fired (fns and theorems). Each
attempt is a rolled-back transaction; on failure the original route or
refusal stands. A top attempt the *kernel* refuses fails the module's
parallel pass and is decided in the serial replay, the same answer at any
width.

**Found on the way**: the planner did not see a self-call written inside a
type (`n = n ∧ E(k)`, a `Type`-valued arm), because `surface::walk_expr`
does not enter types, so it never found the `match` to be a recursion and
let the arm read the top call's `n`: `E(2)` was `2 = 2 ∧ (2 = 2 ∧ True)`. The
meaning check (`--review`) flagged it. The planner's self-call readers now
enter written types (`recursion::type_children`), and such an `E` lowers at
the top with its source's meaning.

**Not retired by this slice**: recursion-case-split-dependent-ih's
`walk_shape` passes `n` unchanged under `match n`, and a `match` does not
substitute its scrutinee variable in the arm, so the call's type is about
`n` while the goal is about `Zero` in every lowering. At the top the ih is
generalized over `n`, so the call fits once the arm's `n` *is* `Zero`; that
is a `match` refinement, not a recursion lowering, and stays with that
issue. Passing the constructor (`walk_shape(k, 0)`) is accepted already.
