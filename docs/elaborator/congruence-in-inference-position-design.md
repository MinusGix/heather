# Congruence in inference position — and what actually blocks the terse spelling

Design doc for the third instalment of `issues/congruence-by-anti-unification.md`,
2026-08-18. The general `cong<A, B>` with an LGG-inferred `f` landed on
2026-08-05 (`crates/elab/src/lgg.rs` plus the `solve_by_lgg` hook in
`apply_implicit`). Since then four consecutive rounds have ranked this issue,
each of them counting the same customer: the standard library declares eight
monomorphic congruence lemmas and applies them 84 times, spelling by hand a
one-place context that the expected type was supposed to determine.

**Nobody had asked why.** This round's first deliverable was that question, and
the answer changed what the round could sensibly build.

## 1. The diagnosis

Each of the 84 sites was rewritten to `cong(p)` — one at a time, so that the
error is attributable — and the failure classified. `lib/std/num/int.hthr`'s 54
sites, the largest and most uniform family:

| outcome | sites | meaning |
| --- | ---: | --- |
| `could not infer the implicit argument f` | 38 | the LGG trigger never fired |
| `cannot generalize` | 16 | the trigger fired and the LGG refused |

So the coordinating hypothesis — *the hook fires only in checking position, and
the library writes its congruences inside `trans` chains* — is **two thirds
right, and the missing third is the one that decides the round**. A third of
the sites are already in checking position, the expected type is already in
hand, and anti-unification still cannot recover the context.

Both buckets were then attacked, in that order, and the second one is a wall.

### 1.1 Why the trigger does not fire (38 sites)

`apply_implicit` consults the expected type — `solve_from_expected`, which
carries the LGG hook — only when the call was *checked*. Inside
`trans(cong(p), q)` the `cong(p)` is an ordinary explicit argument at a domain
`?a = ?b` that no meta has been solved for yet, so it takes the inference
branch and fails before any expected type exists.

Two shapes, and the second is the informative one:

- `cong(p)` **first**: `trans`'s expected type pins `a` and `c` but never the
  middle `b`, so even a hypothetical "propagate the expected type into the
  argument" would hand the LGG a goal `X = ?b` with one endpoint unknown.
  Anti-unification needs *both* sides. Only the sibling argument's type can
  supply `b`.
- `cong(p)` **second**: `c` is determined by the expected type, but
  `solve_from_expected` runs *after* the whole argument loop, so by the time
  the expected type is consulted the argument has already been refused.

Both say the same thing, and it is not "propagate the expected type": it is
**elaborate this argument last**. Which is a mechanism the elaborator already
has (§2).

Six of the 84 are a congruence nested *inside another congruence's* argument.
They are the same shape one level deeper, they are refused before and after,
and they are worth naming only because a scan that skips over a matched call
does not see them — which is how the recorded site counts drifted (§4).

### 1.2 Why the LGG refuses in checking position (16 sites)

These fail for a reason that has nothing to do with position, and it is worth
stating precisely because it is what a reader would otherwise assume away.

    theorem addNat_zero_l(n: Nat): addNat(OfNat(0), n) = OfNat(n) {
        match n { Zero => refl, Succ(k) => cong_int(isucc, addNat_zero_l(k)) }
    }

In the `Succ` arm the goal is `addNat(OfNat(0), Succ(k)) = OfNat(Succ(k))` and
the proof is `p : addNat(OfNat(0), k) = OfNat(k)`. The wanted `f` is `isucc`,
and `isucc` appears in **neither** side of the goal. It appears in the *left*
side after one δι step, and it relates to the right side only by folding
`isucc(OfNat(k))` back up into `OfNat(Succ(k))`. The context is a fact about
conversion, not about syntax.

That is the general shape. A library statement is written in the reader's
terms; the congruence context is a fact about how the two sides *compute*, and
the anti-unifier only sees how they are *spelled*.

The lowering makes it worse rather than better. `List` lowers through the `Wf`
former, so a `match` arm's goal side reads `inr(…; v)` with the payload bound
as one variable while the reduced side reads `inr(…; ⟨a, b⟩)` — convertible by
`Σ`-η, unequal as terms — and one level further down the children of a `Wf`
node are *functions out of `Fin`*, where the two sides differ by a β-redex
against a projection. An anti-unifier that respected `Σ`-η and `Unit`-η was
written and measured during this round: it moved **zero** sites, because the
mismatch has already moved below η by the time it is reached. It was reverted.

### 1.3 What the diagnosis retires

- **`calc` is not the fix here.** A `calc` block puts every step in checking
  position with both endpoints written, which clears the §1.1 bucket in full — and leaves
  §1.2 untouched, because a calc step of `addNat_zero_l` still states its two
  sides in the reader's unreduced terms. Route (b) was a live candidate for
  this round and the data refutes it: `calc` has to be justified by what it
  does for readability, not by this issue's site count.
- **Nothing here argues against the layer-m home.** It argues *for* it, with
  evidence §5 of the issue only asserted: what the library actually needs is
  occurrence selection against a **reduct**, plus a conversion check that the
  abstracted context reproduces the other endpoint. That is `rewrite`, and it
  is not an anti-unifier.

## 2. The mechanism: a result-only implicit is checking-only

`is_checking_only` is the elaborator's answer to "which arguments must be
elaborated last". Its members are the forms whose `elab_infer` arm *refuses* —
`?`, `refl`, a vector literal, an unannotated λ, a bare polymorphic reference.
Deferring exactly those loses no solving power, because in inference mode they
contribute nothing but an error.

`cong(p)` is a form whose `apply_implicit` refuses, for the same reason and
with the same consequence. The set was extended to say so:

> A saturated call `name(a⃗)` whose callee declares an implicit parameter that
> **no explicit parameter's domain mentions** — a *result-only* implicit — is
> checking-only.

`crates/elab/src/lib.rs`, `call_defers_for_result_only`. Three properties of
the test, each of which is a decision:

**It is an occurrence check on the kernel telescope, not on the written type.**
`sym<A>({a}, {b}, p: a = b)` looks, in surface syntax, exactly as
result-only in `A` as `cong` is in `f`. It is not: the kernel's `Id` carries its
type, so `A` occurs in `p`'s domain and an inferred argument solves it. Reading
the surface types would have deferred every `sym` in the library for nothing.
The check substitutes a marker for one binder and asks whether the domain
changed (`mentions_binder`), which is `strengthen_tm`'s trick narrowed from a
suffix of binders to one.

**It is structural, not keyed to `cong`** — the same commitment the 2026-08-05
trigger made. Any declaration whose result type is the only place an implicit
appears benefits; `false_elim<A>(p: False): A` is a second resident.

**It is strictly additive.** A deferred argument that is *syntactically*
checking-only has nowhere else to go: if its obligation never becomes ready,
the call is refused. A result-only call does have somewhere else to go — the
inference path it took before this rule existed. So `DeferredArg` records
which rule deferred it, and an obligation that the fixpoint cannot unblock is
elaborated in inference mode after all, one per pass so the loop's termination
argument survives. Every program that elaborated before this rule takes the old
path and gets the old message; the rule can only add.

Three guards keep calls that infer today off the new path: `@name(…)` fills
everything by hand; a call with **spill** is the curried-tail route, where the
over-applied argument's type is exactly the evidence this test cannot see
(`issues/curried-tail-type-arg-inference.md`); and a **solver** parameter is
filled by resolution, so its being result-only says nothing. `name<…>(…)` needs
no guard — it parses as an `App` whose head is a `TyApp`, which `as_named`
already declines.

### 2.1 The route not taken

Propagating the expected type down into an argument position was the obvious
alternative and it is worse on both counts. It is new machinery of exactly the
kind round two exists to remove, *and* §1.1 shows it does not work: in a `trans`
chain the middle endpoint is not in the expected type at all. Deferral is
existing machinery, and it reaches the middle endpoint because the sibling
argument is what determines it.

## 3. A bounded loosening of "exactly `(s, t)` is `==`"

The 2026-08-05 design's decision 2 — the witness comparison is structural
equality, no conversion — is what keeps this solver linear, terminating and
loud. It stays. What this round adds is a **second attempt**, and only after
the first has failed:

1. the endpoints **as written** (unchanged, and first, so no goal that
   generalized before generalizes differently — reduction can only destroy a
   match, since `f(a) = f(b)` at a transparent `f` unfolds into two
   unrelated-looking bodies);
2. the endpoints in **weak head normal form**, one whnf each.

The witness comparison is still `==`; what reduces is the goal, and only its
two outermost nodes. `s` and `t` are deliberately *not* reduced: the witnesses
come from the proof's type and the goal's payload comes from the statement, and
both are written in the same unreduced terms — reducing one side of that
comparison and not the other is what would break the match.

Why whnf and not conversion: an unbounded `conv` call per `cong` is the
memory-superlinear hazard this project keeps out of the elaborator, and it
would make failure quiet. Two whnfs are linear and terminating, which is the
property the issue's §3 claims for this solver. The cost lands only on the
failure path.

This is what lets `mul(OfNat(m), OfNat(n)) = mul(OfNat(n), OfNat(m))` — which
names no congruence context anywhere in its syntax — reduce to `OfNat(…)` on
both sides and yield `OfNat(□)`.

## 4. What landed, and the honest yield

At `lib/std/num/int.hthr` the three buckets went from (38 refused before the
trigger, 16 refused by the LGG, 0 accepted) to (23, 27, 4): the deferral moved
fifteen sites into checking position, where four of them generalize and eleven
join the wall of §1.2. Across the whole library, 7 of 84 sites accept the terse
spelling.

Two recorded counts were corrected on the way. `int.hthr`'s own comment and the
issue's 2026-08-17 entry both said 58 sites at `Int`; it is 54. And the library
total is 84 rather than the 78 a first scan reports, because a scan that jumps
past a matched call cannot see a congruence nested inside another one.

**The library was deliberately not migrated.** Seven sites out of eighty-four
is not a migration: it would leave every file mixing two spellings, leave all
eight monomorphic lemmas load-bearing, and make the files' own comments about
why they spell it by hand wrong. The numbers are recorded on the issue instead,
and the flipped shapes are covered by tests in the elaborator suite, which is
where a mechanism's evidence belongs when the library cannot yet consume it.

What did land is not `cong`-shaped and outlives the hook: an argument whose
callee cannot infer one of its implicits is now elaborated *after* its
siblings, at the type the call expects. That is a general capability, it is the
answer §1.1 called for, and it is the half of this round that the layer-m
tactic surface does not make redundant.
