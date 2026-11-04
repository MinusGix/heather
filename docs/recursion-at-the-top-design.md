# Recursion at the top: compiling structural recursion against `below`

Status: **decided** (Minus, 2026-11-04): option A, staged as §4 lists;
slice 1 is issues/recursion-below-nat-fallback.md
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
recursion-meaning-check's review mode (`heather check --review`,
`crates/elab/src/meaning.rs`) now tells us when a patch is wrong; it does not
remove the rules.

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
2. *Nat, the default.* After `perf ab`, every `Nat` structural recursion
   lowers by `below`; delete the Nat guard selection and the Nat window
   (`chain_convoy`). Retires cov-window-term-size's Nat half.
3. *Tier-1 `Wf`.* The generic `Below` for chain-shaped and branching `Wf`
   inductives; delete the Wf window and the term comparison. Retires
   cov-window-in-theorem-arms, cov-convoy-motive-second-ambient,
   guard-matches-self-calls-by-term, ih-generalization-under-exists, the rest
   of cov-window-term-size.

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
