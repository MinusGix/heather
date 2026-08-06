# Unifier completeness: postponement, expected-type solving, the pattern guard

Design for the round picking up `issues/elab-unifier-completeness.md`. Round
pattern as usual: this document first, the implementing round against §8's
acceptance list.

**Status: no kernel change is required, and none is proposed.** Everything
below is `crates/elab/src/lib.rs` — the argument loop of `apply_implicit`, the
finalization order around `solve_by_lgg`, one new arm in `elab_infer_at`'s
`Var` case, and two guard tightenings in `unify_tm`/`unify_ty`. The two
invariants of the existing unifier are kept verbatim: **learn-only** (it never
fails from a mismatch, it only records solutions), and **the kernel re-checks
everything** (a wrong solution is a rejection, never unsoundness).

Three measured dents drive the round, all from the issue's log:

- **D1** (2026-07-24): `sym(?p)` is refused — the hole is checking-only, but
  `apply_implicit` infers explicit arguments whose domain still mentions
  metas, so the user must write `@sym(a, b, ?p)`.
- **D2** (2026-08-04): `fn id<A>(x: A) -> A { x }` passed first-class —
  `app1(id, n)` at `app1(f: Nat -> Nat, n: Nat)` — dies as a bare kernel
  `LevelMismatch` on `probe`, with no elaborator message.
- **D3** (standing, from the issue's opening): `unify_tm`'s meta arm checks
  only that the delayed substitution is all-variables, then takes the subject
  verbatim — correct only for a (weakened) identity renaming, and nothing
  states or enforces that.

## 1. What this round decides, and what it does not

Five decisions, in dependency order:

1. **§3 — the slot model.** The per-call solution vector grows a third state:
   a slot is `Unsolved`, `Withheld`, or `Solved(t)`. Deferred arguments and
   flex-applied metas are `Withheld`; `zonked`/`unify_*` treat `Withheld` as
   unsolved-but-untouchable. This replaces `solve_by_lgg`'s `Term::Zero`
   placeholder hack with the same idea made honest.
2. **§4 — per-argument deferral** inside one `apply_implicit` call. An
   explicit argument that is syntactically checking-only and whose domain is
   not yet meta-free becomes an extra scratch-world meta plus a recorded
   obligation, retried after expected-type solving. No cross-call state.
3. **§5 — expected-type-directed solving.** When the call sits in checking
   position with an unspilled spine, its result type is unified against the
   expected type before discharge — the general rule of which `solve_by_lgg`'s
   step-1 harvest is the special case. A bare reference to a polymorphic
   declaration in checking position rides the same path with an empty
   argument list. New guard in `unify_tm`: a pattern `App` whose spine head
   is an unsolved meta learns nothing (the "peeling" hazard `solve_by_lgg`'s
   doc comment records, closed at the source).
4. **§6 — the item-3 finding: permuted renamings are unreachable today.**
   Established structurally and by an instrumented run over the suite (1135
   tests, zero hits). The chosen mechanism is a **guard, not an inversion**:
   the all-vars check is replaced by equality with the weakened identity
   `embed(Γ, d)`, which is exactly the condition under which the existing
   verbatim-take-plus-`strengthen_tm` is correct. The inversion is specified
   (§6.3) but not built.
5. **§7 — diagnostics.** The D2 shape fails, when it still fails, with an
   elaborator message naming the callee and the parameter; D1's obligation
   failures name the argument and the escape hatch. Verbatim texts in §7.

Not in scope, each pointed at its issue in §9: higher-order/flex-flex
unification (`congruence-by-anti-unification`), level-meta inference proper
(`elab-unifier-completeness`, correctly staged behind layer-m), and the
anti-unification congruence's real home (the layer-m goal solver).

The stretch question — route 1's `El(elim …)` application gap from
`indexed-families` (2026-08-04) — turned out to be **already closed** before
this round: see §5.5.

## 2. Diagnosis of D2: the `LevelMismatch` is a missing instantiation, not a level choice

The issue's log guessed "the elaborator picks a level for the instantiation
and the domain wants another". That guess is wrong in a useful way: **no
level is ever picked, because no instantiation is ever attempted.** Verified
by capped run (2026-08-06, `(ulimit -v 8388608 -t 120; target/release/heather
check …)`) and by reading the path:

1. `app1` is monomorphic — no implicit mask — so `app1(id, n)` goes down
   `apply_explicit` (lib.rs ~4392), which elaborates each argument in
   **checking** mode against the callee's domain: `id` against `Nat -> Nat`.
2. `elab_check_hinted`'s fallback (lib.rs ~1875–1888) has no arm for a bare
   `Var`, so it whnf's the expected type, calls
   `elab_infer_at(cx, e, Some(&head))`, and **discards the inferred type**:
   `let (t, _, _) = …; Ok(t)`. There is no elaborator-side conversion check
   anywhere on this path — the kernel is the gate, by design.
3. `elab_infer_at`'s `Var` arm (lib.rs ~2082) is `self.resolve(cx, name,
   e.span)` — the `expected` in hand is not consulted. `resolve` returns the
   committed global **verbatim at its polymorphic type**
   `Π (A : Ty 0). Π (x : El A). El A`. Implicit insertion only exists on the
   `App` path; a zero-argument reference never reaches `apply_implicit`.
4. The kernel then checks the `App` node: the argument `id` infers at the
   polymorphic Π, the declared domain is `Π (Nat). Nat`, and the Π–Π
   conversion rule compares **`dom_level` first** (conv.rs ~658:
   `self.lev_eq(dl1, dl2)?` before the domains): `Ty 0` sits at level 1,
   `Nat` at level 0, so `lev_eq` fails (typing.rs:355) and the whole
   declaration is rejected as `LevelMismatch` — before the domains are ever
   compared, which is why the error names levels and not types.

Same mechanism for the `compose<A,B,C>` variant; `app1(succ1, n)` with a
monomorphic `succ1` never had a mismatch to hit. `app1(id<Nat>, n)` works
today (verified) because `elab_ty_app` performs the instantiation the bare
reference is missing.

**Consequence for scope:** the "narrowest level fix" clause is vacuous — D2
is not a level-choice problem, it is the zero-explicit-argument case of
expected-type-directed instantiation, i.e. exactly item 2's general rule. No
level machinery is touched.

## 3. The slot model: `Sol` with a `Withheld` state

Today `sols: Vec<Option<Rc<Term>>>` carries two meanings for `None`
("unsolved, please learn" and — during `solve_by_lgg`'s harvest, via a
temporary `Term::Zero` planted and removed — "unsolved, hands off"). Deferral
adds a third population that must be visible to `zonked` but untouchable by
`unify_*`. Decision:

```rust
enum Sol { Unsolved, Withheld, Solved(Rc<Term>) }
```

- `unify_ty`/`unify_tm` record a solution only into `Unsolved`.
- `zonked`/`zonked_tm` treat `Unsolved` **and** `Withheld` as unsolved (the
  two-marker device is unchanged; both map to the marker).
- Discharge (`GlobalEntry` construction) requires `Solved` everywhere;
  anything else is the per-slot diagnostic of §7.

**Rejected alternative:** keep `Option` and extend the placeholder hack —
plant `Term::Zero` in every withheld slot for the duration of a harvest. It
works (it is what `solve_by_lgg` does for one slot today) but it poisons
`zonked`: a deferred-argument slot must read as *unsolved* to `zonked` (its
occurrences must block dependent domains), while a placeholder reads as
solved and would substitute a lie into a goal statement. Two different
placeholders for two different lies is where that road goes; the three-state
enum says what is meant.

`solve_by_lgg`'s plant-and-remove becomes `Withheld`-and-`Unsolved`, same
shape, no behavior change; the existing `congruence_lgg.rs` suite pins it.

### 3.1 What a deferred obligation is

A deferred obligation is **not** a first-class constraint in a queue on the
`Elaborator`. It is a record local to one `apply_implicit` activation:

```rust
struct Deferred<'a> {
    slot: usize,        // the extra scratch-world meta standing for the arg
    expr: &'a Expr,     // the unelaborated surface argument
    dom: Type,          // its declared domain, scratch world
    dom_level: Level,
    param: usize,       // parameter index, for the hint and the message
}
```

The scratch world is the constraint store: the domain's meta occurrences
*are* the "blocked on" set, and `zonked` already decides readiness exactly.

**Rejected alternative: a cross-call constraint queue on the `Elaborator`.**
The architecture is per-call scratch worlds — the `n` metas take the
innermost Ψ indices, committed globals shift up by `n`, and one
`GlobalSubst` discharges the block before `apply_implicit` returns. A
surviving constraint would carry scratch-world indices out of the world that
defines them, and every consumer of Ψ arithmetic (`resolve`'s `goal_base`
offsetting, `shift_global` at each argument, the discharge renumbering)
would need to know about it. No measured dent needs it: D1, D2 and every
log entry in the issue are single-call shapes, and a *nested* call inside an
argument elaborates to completion (or errors) inside its own world before
the outer loop continues — there is nothing an inner call could leave
pending that the outer call could later unblock, because the outer call's
metas are not in scope in the inner world at all. If a program ever needs
cross-call propagation it will look like an inner "could not infer" whose
answer arrives outside; file it against the issue when it exists.

## 4. Per-argument deferral

### 4.1 Trigger

In `apply_implicit`'s argument loop, an explicit argument is deferred exactly
when **both** hold:

1. its domain is not yet meta-free (`zonked(&dom, …)` is `None` — the same
   test that today routes to inference mode), and
2. the argument is **syntactically checking-only**: `Hole`, `Refl` (when not
   shadowed), `AutoRefl`, `VecLit`, a `Lam` with any unannotated binder,
   `FZ`/`FS`/`absurd` heads (under their existing not-shadowed/not-a-ctor
   guards), **a bare reference to a global with a leading implicit prefix**
   (the §5.3 route's precondition; added by the implementing round — see
   below), and `Num` is *excluded* (it infers at `Nat` today and that
   default is load-bearing for the suite).

The set is a predicate `fn is_checking_only(&self, cx: &Cx, e: &Expr) ->
bool` next to the loop, with a doc comment tying each variant to the arm in
`elab_infer_at` that refuses it. These forms cannot contribute a solution in
inference mode anyway — today they *error* there — so deferring exactly them
loses no solving power.

**Amended while implementing (2026-08-06): the bare implicit-prefix
reference joins the set.** It is the one member that *can* infer — but only
at its uninstantiated polymorphic Π, which against a meta-bearing domain can
just mis-teach: `call<A>(f: A -> A, x: A)` fed `call(id, x)` unified
`El ?A ≟ Ty 0` and "solved" `?A := ⌜Type 0⌝`, ending in the same bare kernel
`LevelMismatch` D2 diagnoses — with `f` *first*, before `x` could solve `A`.
Deferring it routes the retry through the §5.3 checking route once the
domain zonks, and turns the never-zonks case into the §7.2 message instead
of a junk instantiation. At a meta-free domain it is checked inline like
every other member, which is the D2 path unchanged.

**Rejected alternative: defer any argument whose domain has metas.** That
would defer `a` in `sym(p)`… no: it would defer `p` in `@sym(a, b, p)`-less
calls generally — the *inference* of ordinary arguments against meta-bearing
domains is the primary solving channel (`unify_ty` on the inferred type is
how `A`, `a`, `b` get solved at all). Deferral must be the exception for
forms that cannot infer, not the rule.

**Rejected alternative: try inference and defer on error.** Error-driven
control flow would have to distinguish "checking-only refusal" from a real
error inside the argument by matching message strings or adding an error
variant, and it would run arbitrary elaboration work before undoing it. The
syntactic set is closed, small, and already enumerated by the refusing arms.

### 4.2 Mechanism

The scratch world is sized up front:

> `n` = (implicit parameters in the mask) + (explicit arguments that are
> syntactically checking-only).

The second summand is an over-approximation — a checking-only argument whose
domain turns out meta-free is checked inline exactly as today, and its
pre-allocated slot is filled with the checked term immediately (a solved slot
is indistinguishable from an unused one at discharge). Counting up front
keeps `n` static, which everything downstream of `shift_global(n)` assumes.

When the trigger fires, the argument's spine position is filled with a fresh
meta `?d^{id_Γ}` (built exactly like an implicit's, lib.rs ~4628), the slot
is set `Withheld`, and the obligation is pushed. The loop continues; later
arguments whose domains mention the deferred *value* see `?d` and behave
correctly (their `zonked` fails, they defer or infer as their own trigger
says; the harvest cannot touch `?d` because it is withheld).

### 4.3 Retry policy and termination

Finalization order in `apply_implicit` (this is the (a)/(b)/(c) ordering the
round scope asks to be thought through):

1. the argument loop, with deferral (§4.2);
2. expected-type solving (§5), gated as today on `expected.is_some() &&
   spill.is_empty()` — for `sym(?p)` the endpoints come from here and
   nowhere else, which is why deferral alone was never sufficient;
3. **retry the deferred obligations, to fixpoint in argument order**: for
   each obligation whose slot is still `Withheld`, `zonked(&dom)`; if
   meta-free, `elab_check_hinted` the expression against it (the hole
   becomes an ordinary goal here, `refl` gets its `Id`, the vector literal
   its `Vec`), shift the result by `n`… no — record the *committed-world*
   term as the slot's solution (solutions are committed-world payloads, the
   same convention `unify_*`'s strengthened subjects already follow). Repeat
   passes while at least one obligation resolved and any remain;
4. discharge, then spill, unchanged.

Termination: the obligation list is fixed after step 1; each pass either
moves at least one slot `Withheld → Solved` or stops; slots never move back;
so at most `k` passes for `k` obligations. Step 3 cannot create new
obligations or new solutions for *other* metas — checking-mode elaboration
returns a term and never writes `sols` — so the fixpoint is real, and the
multi-pass exists only for the case where obligation `i`'s domain mentions
deferred value `j` (either order), which a single ordered pass would
misreport.

**Rejected alternative: retry on every new solution during the loop.** More
eager, no additional completeness: solutions arrive from argument inference
(during the loop) and from the expected type (after it); an obligation
solvable at all is solvable when both sources have run, and the sources do
not consume obligations. One consolidated retry point is also the only place
the "which implicit is missing" diagnostic can be stated truthfully.

## 5. Expected-type-directed solving

### 5.1 The rule

> When an implicit-inserting call sits in checking position and its spine is
> unspilled, unify its (scratch-world) result type against the whnf'd
> expected type — learn-only, before discharge.

Concretely, in the finalization block that today runs `solve_by_lgg`:

```text
if expected && spill.is_empty() && any slot unsolved:
    read the LGG trigger off `ty` (unchanged, solve_by_lgg's step 0)
    if it fires: withhold ?f, harvest, LGG-abstract   (existing path)
    else:        unify_ty(&cx.gamma, &ty, expected, n, 0, &mut sols)
```

The general harvest is *the same call* `solve_by_lgg` already makes as its
step 1; what changes is that it now runs even when the flex-`Id` trigger does
not fire. For D2's bare reference (§5.3): pattern `Π (x : El ?A). El ?A`,
subject `Π (Nat). Nat` — the Π congruence descends, the El rule fires,
`?A := ⌜Nat⌝`, and the kernel accepts the instantiated call. For D1: pattern
`Id(El ?A, ?b, ?a)`, subject `Id(Nat, 0, n)` — `?A`, `?a`, `?b` all solve,
and the retried hole gets the meta-free statement `n = 0`.

### 5.2 Relation to `solve_by_lgg`: coexist, with the LGG preceding

Decision: **coexist**; the LGG trigger is read first and keeps priority for
its shape; the general harvest is the else-branch *and* remains embedded as
the LGG path's step 1. Subsumption in either direction was rejected:

- The general rule cannot subsume the LGG: `?f(s) ≟ X` is outside the
  Miller fragment (`congruence-by-anti-unification` §2) and no first-order
  harvest reaches it; the LGG *is* the rule for that shape.
- The LGG hook cannot subsume the general rule: its trigger is deliberately
  narrow (flex-`Id` both sides), and widening it would smear a documented
  throwaway (`solve_by_lgg`'s own doc comment: deleted when the layer-m
  solver lands) across a permanent behavior.

The comment block at lib.rs ~4827 ("Nothing else gets to consult the
expected type… solving result-only implicits *in general* is
elab-unifier-completeness's question") is this round's question answered; the
comment is rewritten to point here. (As shipped, `solve_by_lgg` is renamed
`solve_from_expected` — it now carries both rules, the LGG trigger first and
the general harvest as the else branch; the LGG half keeps its documented
throwaway status.)

### 5.3 The zero-explicit-argument case (D2)

A bare `Var` reference to a declaration with a non-empty implicit mask, met
in **checking** position, is routed through the same machinery with an empty
spine. In `elab_infer_at`'s `Var` arm (lib.rs ~2082): when the name resolves
to a committed global (locals, aliases, and constructors keep their existing
precedence — the check runs only after `resolve`-order says the global
wins), the mask's **leading implicit prefix** is non-empty, and `expected`
is `Some`, call `apply_implicit` with `args = []` and the mask cut at the
first explicit parameter. The loop mints metas for the prefix, consumes no
arguments, the harvest solves what the expected type determines, discharge
yields the instantiated head at the remaining Π.

Two details:

- **The mask is a prefix here, a suffix everywhere else.** `apply_implicit`
  currently *recovers* its parameter offset as
  `all_params.len() - mask.len()` in two places (lib.rs ~4618, ~4724),
  which is only right for suffixes. The offset becomes an explicit
  parameter, passed as `tyargs.len()` by the `f<T>(…)` path and `0` here —
  the same honesty `apply_explicit` already practices with `param_offset`.
- **Inference position is unchanged.** A bare `id` with no expected type
  still resolves to the polymorphic value verbatim; there is nothing to
  solve from, and today's behavior (later kernel gating if misused) stands.
  The dent was checking position, where the information exists and was
  discarded.

**Rejected alternative: instantiate in `elab_check_hinted`'s fallback**
(unify the inferred type against `expected` after any `elab_infer_at`). That
would silently add expected-type solving to *every* expression's checking
fallback, not just implicit-inserting heads — a much wider behavioral
surface, most of it dead (no metas in scope), some of it live in ways no
dent motivates. The `Var` arm change is exactly the measured gap.

### 5.4 The flex-head guard in `unify_tm`

`solve_by_lgg`'s doc comment records the hazard: `unify_tm`'s `App`
congruence, meeting pattern `?f(?a)` against subject `add(a, a)`, "solves"
`?f := add(a)` by peeling — satisfying one endpoint, contradicting the
other, and reaching the kernel as `NotConvertible` on a term nobody wrote.
Today that is fended off per-site by withholding `?f`. The general harvest
multiplies the sites, so the guard moves to the source. Decision: in
`unify_tm`'s `(App, App)` arm, if the **pattern's spine head** is an
unsolved (or withheld) meta of this call (`var.0 < n`), learn nothing from
this node — return. Flex-headed applications are outside the Miller
fragment; the only rule trusted for them is the LGG, and now no path can
reach them first. This is a strict narrowing of what gets *learned*, which
the learn-only contract always permits.

Risk, named for the implementing round: committed globals in the scratch
world have `var.0 >= n`, so `D#fam`-headed family spines (which the
`type-arg-inference-through-index` walker relies on) are untouched by the
guard; `implicit_args.rs` pins that and must stay green.

### 5.5 The stretch question is already closed

The route-1 application gap measured 2026-08-04 (`len<A>(n, v: V<A>(n))`
applied at a concrete instance cannot solve `A`) **no longer reproduces**:
both the open-data and constructor-literal probes elaborate and kernel-check
today (capped runs, 2026-08-06, scratchpad `probe6/probe7.hthr`). The closer
was not this round's machinery but `type-arg-inference-through-index`
(closed 2026-08-05): `unify_tm` grew congruences for `ElimNat` and the
type-code constructors, which is exactly the "nothing structural in
`El(elim …)`" hole the measurement hit, plus the kernel-def round's `D#fam`
re-keying for the unparameterized class. Nothing in this design needs
widening for it; the indexed-families issue should note the gap closed
en passant.

## 6. Item 3: the Miller pattern guard

### 6.1 Finding: a non-identity all-vars renaming is unreachable today

**Structural trace.** A meta occurrence is born as `?m^{id_Γ}` at exactly one
site (lib.rs ~4628; goals are the same shape via `new_goal`), with Γ the
call's context, which does not change for the duration of `apply_implicit`.
Every transport an occurrence undergoes composes its delayed substitution
with maps that are **identity on Γ**:

- `cod.apply_local(id_Γ.extended(arg))` at each parameter (lib.rs ~4689,
  ~4567, ~4420) — Γ entries map to themselves; only the consumed binder gets
  a payload;
- weakening when a payload is spliced under binders inside a type
  (`apply_local`'s lifting) — order-preserving by construction;
- whnf/β during `self.whnf` of the evolving type — every substitution
  reduction performs is `id` on Γ extended at the redex's own binders.

Composition therefore keeps each occurrence's renaming a *weakened
identity* — `Γ`'s variables in order, shifted by the binders above the
occurrence — or introduces a non-variable payload (when the occurrence's
scope actually mentioned a consumed binder), which the existing all-vars
check already declines. No reachable map reorders Γ (no permutation),
duplicates an entry (a duplicate would need some σ sending two Γ-variables
to one, and every reachable σ is `id` on Γ), or drops one.

**Empirical check.** `unify_tm`'s meta arm was temporarily instrumented to
report any all-vars occurrence whose substitution differs from
`embed(gamma, d)` (the weakened identity at the traversal depth). Full
`scripts/test --fast` run, 2026-08-06: **1135 tests passed, zero reports.**
Instrumentation reverted; the transcript is the round record, not the tree.

### 6.2 Decision: the guard, and why not the inversion

The all-vars check in `unify_tm`'s meta arm — and its twin inside the El
rule in `unify_ty` (lib.rs ~5458) — is replaced by

```rust
*subst == embed(&gamma, d)
```

(`embed` at `d = 0` *is* `LocalSubst::id`, so `solve_by_lgg`'s existing
trigger comparison is already the same test at depth 0.) This is precisely
the condition under which the current behavior is a theorem rather than an
assumption: for an occurrence `?m^{embed(Γ,d)}` and a subject `s` with
`strengthen_tm(Γ, s, d) = Some(s₀)`, the recorded solution `?m := s₀`
satisfies `s₀[embed(Γ,d)] = s₀.shift(d) = s` — the verbatim take *plus the
strengthening that already runs* is the inversion, for exactly this class of
renaming. Distinctness and order come free (a weakened identity is distinct
and ordered by construction), so the Miller side conditions are discharged
by one equality against a substitution the file already knows how to build.

**Rejected alternative: implement the permuted-renaming inversion now.** It
would be code with no reachable input (§6.1), untestable end-to-end — the
same reason `type-arg-inference-through-index` reverted its two prototyped
shapes as "untestable on today's lowerings". A guard that declines is
learn-only-correct forever; an inversion that cannot be exercised is an
unstated assumption with extra steps.

### 6.3 The inversion, specified for the day it is reachable

Recorded so the guard's decline has a named successor. If a distinct-vars
permutation `δ` ever reaches the arm (plausible source: metas minted under
binders pushed *during* a future elaboration form): build `δ⁻¹` as a
`LocalSubst` sending `Var(j)` to `Var(i)` for each `terms[i] = Var(j)`
(partial where `δ` drops variables — a dropped position takes a marker),
set the candidate `s₀ = s.apply_local(δ⁻¹)`, and accept it iff
`s₀.apply_local(δ) == s` — the marker-comparison idiom of
`strengthen_tm`/`zonked` rather than a hand-written occurs traversal, per
the file's stated preference (the round-trip fails exactly when `s` mentions
a variable outside `δ`'s image, which is the scope check). Non-distinct or
non-var entries keep declining.

## 7. Diagnostics

All messages elaborator-level, `ElabError::Elab`, at the call span unless
noted.

1. **Bare polymorphic reference, implicit undetermined by the expected type**
   (D2's failure mode after the fix; checking position only — inference
   position keeps today's behavior and today's messages):

   > cannot infer the type argument \`A\` of \`id\` from the expected type
   > here — write \`id<…>\` to give the type arguments

   (Value-implicit variant: "could not infer the implicit argument \`a\` of
   \`sym\` from the expected type here".)

2. **Deferred obligation still blocked at discharge** (at the *argument's*
   span, one per obligation, before the generic unsolved-meta report so the
   user sees the argument and not only the meta):

   > this argument of \`sym\` was deferred — the type of its parameter
   > \`p\` still mentions an implicit that could not be inferred; give the
   > type arguments (\`sym<…>(…)\`) or write the call fully explicitly
   > (\`@sym(…)\`)

   (As shipped: the explicit-call escape is spelled \`@sym(…)\` — the
   argument tuple of the original draft is not reconstructible generically.)

3. **Existing messages unchanged**: "cannot infer the type argument \`A\` of
   \`f\` here — no argument's type mentions it; write \`f<…>(…)\`…" still
   fires for calls with arguments where the harvest also found nothing (it
   is now literally true only after the expected type has been consulted,
   which is the point); the hole/`refl`/`FZ`/vector-literal
   inference-position refusals in `elab_infer_at` keep their texts and their
   tests — they now fire only in genuine inference positions, since the
   argument-position route defers instead.

4. **The D2 guarantee stated honestly:** the repro now either elaborates
   (`?A := ⌜Nat⌝`, kernel accepts) or fails with message 1. A bare kernel
   error remains possible on this path in one narrower case — the harvest
   *solves* the implicit and the solution is level-wrong for the parameter
   (e.g. a level-1 instantiation of an `A : Ty 0`) — because learn-only
   never verifies. That is level inference's residue, §9.

## 8. Test plan

Per `docs/testing-generated-terms.md`'s axes where they apply (this round's
outputs are solutions and goals rather than generated schemas, so axes 1–4
are read as: literal *and* neutral solution sources, an open element type,
checking *and* computation position, negative controls).

**`crates/elab/tests/goal_holes.rs`** — D1 acceptance:
- `sym(?p)` elaborates as a goal named `p`, statement `n = 0`, discharged by
  `on ?p := …` — the round's acceptance test; the MVP-restriction pin that
  asserts the refusal is retired and replaced, not deleted silently.
- Neutral endpoints: `sym(?p)` at `add(n, m) = k` (endpoints neutral terms).
- Open element type: `sym(?p)` where the `Id`'s type is a bound `A : Type`.
- Deferral order: an obligation whose domain mentions a *later* argument's
  solution (`@`-less `trans(?p, q)` shape), and the two-obligation fixpoint
  case. (The draft asked for "both directions of inter-obligation
  dependency"; a telescope only ever depends *forward*, so the
  backward-dependent obligation is not constructible — an obligation's
  domain is read at its own step and can only mention metas minted earlier.
  The multi-pass loop stays as §4.3 specifies, the reachable dependent case
  — a later obligation's domain mentioning an earlier obligation's value —
  is the one pinned.)
- Negative: `sym(?p)` in inference position (unannotated `let`) errors with
  **message 2**, not the old hole refusal — deferral is per-argument
  (§4.1's trigger does not consult the position), so the argument-position
  route defers there too and blocks at the missing expected type, exactly as
  §7.3 states; the `elab_infer_at` refusals keep firing in *genuine*
  inference positions (`let x = ?;`, `match ?`). (The draft of this bullet
  said "the existing hole message", contradicting §7.3; corrected while
  implementing.) A call whose endpoints the expected type does not determine
  (`trans(?p, ?q)`) gets message 2 verbatim.

**`crates/elab/tests/polymorphism.rs`** — D2:
- The issue's repro `app1(id, n)` elaborates and kernel-checks; the
  `compose<A,B,C>` variant likewise **at a written instantiation**
  (`compose<Nat, Nat, Nat>(id, id, n)` — concrete domains, both bare `id`s
  down the checking route); both in computation position (`fn … -> Nat`) and
  in checking position under a `theorem` statement. The fully inferred
  `compose(id, id, n)` is pinned as a *negative* with message 2: `compose`'s
  `B` is determined by neither `n` nor the expected type, and solving it
  from the deferred `id`s would be cross-call propagation, which §3.1
  deliberately does not build.
- A bare reference whose expected type is *another* polymorphic Π (open
  element type: `f: A -> A` parameter fed `id`).
- Negative: bare `id` bound by unannotated `let` (inference position) keeps
  today's behavior; a bare reference against an expected type that does not
  determine `A` fails with message 1, not a kernel error.
- Kernel-gate control: a look-alike where the harvest's solution is wrong by
  conversion is still rejected by the kernel (the learn-only guessing case),
  asserting the *kernel* error — the pin that the gate did not weaken.

**`crates/elab/tests/implicit_args.rs`** — the harvest and guards:
- The declared-index and forded positives and the look-alike negative stay
  green under the flex-head guard (§5.4's named risk).
- A direct unit-ish pin of the flex-head guard: a call whose result type is
  `?f`-applied does not get `?f` peeled by the general harvest (observable:
  message, not `NotConvertible`).

**`crates/elab/tests/congruence_lgg.rs`** — unchanged behavior: all 16 pins
stay green across the `Withheld` refactor and the finalization reorder; the
LGG-trigger-precedes-harvest order gets its own pin (a shape matching both
the trigger and a first-order solution must take the LGG).

**`crates/elab/tests/determinism.rs`** — the new solving is ordered and
structural; the determinism suite runs unchanged.

Vector-literal and `refl`-in-argument deferral each get one positive
(checking-only form at a meta domain solved by a later argument) and share
the negative controls above. Final verification is a plain full
`scripts/test` (prelude and lib are touched via the paths, not the files —
but the rule is the rule).

## 9. What this does NOT fix

- **Flex-rigid outside the Miller fragment** — `?f a ≟ X` with `a` an
  arbitrary term stays with `issues/congruence-by-anti-unification.md`; the
  LGG hook remains the only rule for its one shape, and §5.4's guard now
  *enforces* that nothing else pretends to the position.
- **Level-meta inference proper** — no level unification exists after this
  round either; the harvest can still hand the kernel a level-wrong
  instantiation (§7.4). Correctly staged behind layer-m
  (`issues/elab-unifier-completeness.md`, level bullet, which stays open).
- **The anti-unification congruence's real home** — the layer-m goal solver,
  occurrence selection, `rewrite`
  (`issues/congruence-by-anti-unification.md`); `solve_by_lgg` is still the
  documented throwaway.
- **Cross-call postponement** — deliberately not built (§3.1); if a dent
  ever demands it, it is a new design against the per-call-world invariant,
  not an extension of this one.
- **Elaborator-side conversion checking in general** — an ordinary
  ill-typed argument still surfaces as a kernel error; this round adds
  messages only where implicit machinery is involved
  (`issues/cli-check-diagnostics.md` / `issues/diagnostics-name-the-written-form.md`
  own the general story).
