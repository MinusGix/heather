---
title: Bare constructors resolved by the expected type in checking position
status: closed
labels: [frontend, elaboration, ergonomics, modules]
created: 2026-08-05
updated: 2026-08-16
---

**Closed 2026-08-16.** Built as specified; see the Log. The residue found on
the way out is a *different* subsystem and left with its own owner
([[deep-pattern-ctor-needs-column-type]]) rather than keeping this open.

The follow-up `docs/language/modules-design.md` §4 promised an owner for: in
checking position the expected type names the inductive, so a bare `None`
at expected `Option<A>` is unambiguous whatever is in scope — the
bidirectional elaborator already holds the evidence. Synthesis position
keeps requiring uniqueness or qualification (`Option::None`).

This is the third instance of the one-resolution-judgment direction (doc
§8): `.` fields/methods are receiver-directed, match arms are
scrutinee-directed (landed with v1 — arms position within the scrutinee's
declaration), and this is expected-type-directed. It is also what finally
deletes the historical "constructor names globally unique" constraint
rather than merely scoping it per-module.

Bounded by the doc's two invariants: checking position may *shrink* the
candidate set, never reinterpret — a bare constructor that checks today
must mean the same declaration after any import is added.

## When

Triggered: the first time a real file has to qualify a constructor that
checking position already determines — or the notation/typeclass round,
which wants the same judgment for operators and should build them
together.

## What it assumes from elsewhere

- **[[modules]]** owns the name regime and the qualification escape
  hatch. Assumed here: only that `Type::Ctor` qualification stays.

## Log

### 2026-08-16 — landed, and the invariant that sized it

The judgment is `Elaborator::ctor_here_expected` (`crates/elab/src/lib.rs`),
consulted from `elab_check_skel`'s two constructor arms and from its three
`FZ`/`FS`/`trivial` guards, which asked the same question with less evidence.
It shares `arm_ctor_index` with the `match` arm route, so the two type-directed
constructor resolutions are one function and the `Option::None` spelling costs
nothing extra at either. `expected_ind` peels an expected `Π` before reading the
tag, because an unsaturated constructor is checked against the function type it
η-expands into ([[constructors-as-function-values]] §2) — the declaration is in
the codomain.

**The design content is the two guards, not the lookup.** The lookup is four
lines; what the round actually decided is when it is allowed to fire, and the
first cut got it wrong in a way a test caught:

1. **Fallback, never first.** The ordinary reading is tried first, so a name
   that resolves today keeps its declaration and the expected type only settles
   what the name layer left unsettled.
2. **Every visible candidate must be a constructor** (`only_ctors_visible`).
   This is the one that was missing. A `fn None() -> Option<Nat>` is exactly as
   admissible at an expected `Option<Nat>` as the constructor is, so the type is
   *not* evidence between them; firing anyway would take a file that means the
   function today and silently make it mean the constructor the moment a second
   `None` became visible — precisely the reinterpretation
   `docs/language/modules-design.md` §8's second invariant forbids. The route is worth
   having only because it is honest about when it does not apply.
3. **A binder still wins**, at every expected type. The shadowing check is
   repeated inside the route rather than inherited, so the type evidence cannot
   buy that precedence back.

Synthesis position is untouched: invariant 1, not an omission — and it has a
consequence a writer meets before they meet the feature: whether an **argument**
is checking position depends on the parameter, not on the call. `mono(None)` at
`fn mono(o: Option<Nat>)` is settled; `unwrap_or(None, 9)` at
`fn unwrap_or<A>(o: Option<A>, …)` is not, because that argument is where `A`
comes from. Pinned in both directions, because the difference is invisible in
the source.

Tests +6 in `crates/elab/tests/modules.rs`, each written at **both** colliding
declarations in one file — a test at one of them passes under "pick the first
`None` you find", which is the first-match regime §4 refuses. Both positives
were confirmed to fail with the route disabled, and the invariant-2 control was
confirmed to fail with guard (2) disabled — it is the test that caught the first
cut, not a decoration. The `Π` peel was mutation-checked the same way, after
the first fixture turned out not to exercise it at all: `Some` collided with
nothing, so `fn mk() -> Nat -> Option<Nat> { Some }` was resolving by the
ordinary route and the test was passing for the wrong reason. The colliding
declaration now shares `None` *and* `Some`. The pre-existing
`a_constructor_declared_in_two_modules_is_ambiguous_until_qualified` pinned the
old behaviour and was **deliberately rewritten**, not re-baselined: its checking
half is now the positive, and what survives moved to synthesis position under a
new name, on a monomorphic pair of declarations (a nullary constructor of a
*parameterized* type cannot synthesize at all, so `Option::None` there would
have been refused for a reason that has nothing to do with names).

**Found in passing, filed rather than fixed**, and it is the same family:
[[deep-pattern-ctor-needs-column-type]]. `patterns.rs:is_ctor_name` classifies a
bare identifier inside a deep pattern with no type evidence, so an ambiguous
name becomes a *binder* silently — a live violation of invariant 2, verified
with a throwaway test (the arm goes dead and the failure surfaces as a kernel
`NotConvertible` several steps downstream). Not fixed here because it is not
this issue's judgment and not a threading job: `reclassify` runs before
`matrix`, deliberately, and a column's type does not exist until after.

Verified on the final tree: suite 1671 -> 1677, full run, 0 failed;
`scripts/bench --check` 18 comparisons within thresholds.
