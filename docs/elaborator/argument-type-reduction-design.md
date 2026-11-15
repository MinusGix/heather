# Reading implicit arguments off an argument type that reduces

Design doc for `issues/motive-application-hides-hypothesis-type.md` (ranked #2
by the `Int` round, eight sites in `lib/std/num/int.hthr`), landed 2026-08-17. The
claim being designed: **an argument's type is evidence even when it is a
redex** — the third instalment of the sentence `issues/curried-tail-type-arg-
inference.md` and `issues/match-arg-of-polymorphic-callee-needs-motive.md`
landed earlier the same day ("…even after the parameters run out").

## 1. The refusal

A hand-written induction principle over a non-recursive inductive has to take
its motive as a **value parameter**, because there is no structural recursion
to hang a `match` motive on:

    theorem int_ind(P: Int -> Type, z: P(OfNat(0)),
                    up: (k: Nat) -> P(OfNat(k)) -> P(OfNat(Succ(k))), …)

So a step arm's hypothesis is bound at `P(OfNat(k))`, and once `P` is the λ the
call supplied, that type *is* a β-redex:

    ih : (λ (z: Int) => add(a, z) = add(z, a))(OfNat(k))

Implicit arguments are solved by `unify_ty`, a structural, learn-only walk of a
parameter's domain against the argument's inferred type. Against `Id(Int, ?a,
?b)` this subject is `El` of an application whose head is a λ — no congruence
rule matches, nothing is learned, and the call is refused with "could not infer
the implicit argument `b` of `cong_int`". The same for `sym(ih)`, which is what
establishes that the defect is in *reading an argument's type* and not in one
congruence lemma.

The workaround was to restate the hypothesis inside the call:
`@cong_int(isucc, add(a, OfNat(k)), add(OfNat(k), a), ih)`.

## 2. Where to reduce

Two places could fix this, and they are not the same size.

### 2.1 At the read site (chosen)

`unify_ty` is called on an argument's inferred type in exactly two places, both
in `apply_implicit`: the declared-parameter loop and the spilled-argument loop
that `curried-tail-type-arg-inference` added. Reducing there fixes *every*
consumer at once — `cong_int`, `cong_list`, `sym`, and anything a library
writes tomorrow — because none of them knows how its implicits were found. It
also composes with what is already one line below: `solve_from_expected` whnf's
the **expected** type before its harvest, for the same reason and with the same
learn-only discipline. This route makes the two sides of the elaborator's
evidence say the same thing.

### 2.2 At the binder (declined)

The issue's alternative: when a λ binder carries a written annotation that is
convertible to the expected parameter type, let the *annotation* be what enters
the context. Narrower, and it has a real second argument in its favour — a
context entry then prints as the writer wrote it.

It was declined on two counts.

**It fixes a spelling, not a class.** Only hypotheses that a writer thought to
annotate are helped. The same redex arrives unannotated from a `let`, from a
function returning `P(x)`, and from a `match` arm whose goal is a synthesized
motive applied — none of which has a binder to annotate.

**Its second argument is not real.** Goal-hole context entries are *already*
displayed reduced: `display_type`'s reader stage unfolds enough to give a head,
so the hole in a step arm lists the equation and not the redex — measured
2026-08-17 while designing this, against a `?step` in exactly the arm the issue
is about. The entry a reader sees is therefore the same under either route, and
the binder route would buy display nothing while leaving `sym` unfixed.

(What the probe printed was `ih : add(ih, 0) = ih` — reduced, and naming the
wrong binder. That is a real display defect *next to* this one, filed as
`issues/goal-context-entry-printed-in-the-wrong-context.md`: an entry's type is
rendered against the whole of Γ rather than against the prefix it is scoped in,
so `p : add(a, 0) = a` prints as `add(p, 0) = p`. Pre-existing, general — it
has nothing to do with redexes — and owned by that issue.)

## 3. What landed

`Elaborator::unify_arg_ty`, called from both read sites:

    the syntactic read      →  learned something?  →  done, old path exactly
                            →  learned nothing     →  read the whnf too

Three properties, and they are what keep this from being a widening:

- **Learn-only, twice.** `unify_ty` records into `Unsolved` slots and never
  fails. The retry can add solutions; it cannot retract or contradict one, and
  a wrong solution is a kernel rejection as it always was.
- **No progress is the trigger**, not "something is still unsolved". An
  argument whose type taught *anything* takes the path it took before this
  existed, so no call that already elaborated reaches the reduction. That is
  also the whole of the performance story: the added work on a succeeding call
  is one `count()` over `sols` (length = the call's implicit count, typically
  two or three), and the reduction itself runs only on calls that were headed
  for a refusal.
- **The reduction is opportunistic.** `whnf` is fuel-bounded, and out of fuel is
  swallowed rather than raised: the honest report for a hypothesis nobody asked
  to reduce is the caller's own per-slot "could not infer" message, not a
  complaint about fuel. Termination is the fuel's, so a type whose normal form
  is still not an `Id` reports rather than loops.

Weak head normal form and not full normalization: the read needs the type's
*former* — `Id`, `Vec`, an inductive's `El` code — and `unify_ty` descends into
the arguments itself, where a meta meets whatever term is there and solves to
it. Normalizing deeper would change which term a solution is spelled as, for no
extra evidence.

## 4. What it collected

`lib/std/num/int.hthr` lost **all twenty-two** of its `@cong_int(f, lhs, rhs, p)`
spellings, and the split between them is a finding of its own:

- **Eight** are the issue's: `add_comm`, `add_assoc`, `neg_add` and
  `mul_add_distr`, two arms each, every one of them `cong_int(…, ih)` at a
  motive-applied hypothesis. These are what this change bought.
- **Fourteen** are not. Their proof argument was an ordinary lemma call at a
  real `Id` (`add_neg(y)`, `mul_ofnat_succ(a, k)`, `mul_comm(c, a)`, …), so
  nothing was ever hidden and the endpoints never had to be written. Verified
  by running the library with the reduction disabled: all fourteen check terse
  on the old elaborator. They were spelled out for consistency with the arms
  that had to be, which is how a real tax spreads past its own sites — and the
  reason the issue counted ten rather than eight.

## 5. What this does not do

- **A redex under a former is not reduced.** `unify_ty` descends structurally,
  and the retry supplies a weak head normal form at the *top* only. A subject
  like `List<(λ …)(k)>` meeting a rigid `List<Nat>` still teaches nothing.
  Nothing wants this yet: a motive application is the whole type of the
  hypothesis, never a component of it.
- **Nothing reduces the parameter's domain.** The pattern side is scratch-world
  syntax the declaration wrote, and reducing it would change which meta a
  solution lands in. Only the subject reduces.
- **A checking-position argument is untouched**, and needs to be: at a meta-free
  domain the argument is *checked*, and conversion reduces on both sides
  already — the redex was never a problem there. It is only inference-mode
  reading that had no reduction in it.
