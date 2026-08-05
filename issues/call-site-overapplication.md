---
title: Over-application spills into curried application: nth(t, k)
status: closed
labels: [frontend,elaboration,ergonomics]
created: 2026-08-05
updated: 2026-08-05
---

Small round item (2026-08-05 ergonomics round). Surface calls are already
multi-argument (`append(xs, ys)` works); the ugly case is a fn that is
*curried by necessity* — `std/list.hthr`'s `nth<A>(xs: List<A>) -> Nat -> Option<A>`,
curried because the termination checker wants one decreasing argument with the
rest fixed. Callers must write `nth(t)(k)`.

The slice this issue owns: at a call site, when `f(a1, …, an)` supplies more
arguments than `f`'s parameter arity, spill the excess into iterated
application — `nth(t, k)` elaborates as `nth(t)(k)`. Call-site only; no
change to declarations, lowering, or the kernel term produced.

Why it stays worth having even after the definition-site fix: partial
application chains and any fn-returning fn benefit, not just the
termination-shaped ones; and it makes `t.nth(k)` (receiver desugaring plus
spill) read right immediately.

## Design (2026-08-05)

**Where the hook goes.** Nowhere new: `apply_explicit` (crates/elab/src/lib.rs)
already walks the Π spine one argument at a time and re-reads the callee's type
after each step, so `nth(t, k)` at a callee with no implicits *already*
elaborates as `nth(t)(k)` — the second argument simply meets the `Nat ->
Option<A>` that the first one produced. The only place over-application is
refused is `apply_implicit`'s saturation check: after the implicit mask is
consumed it does `if args.next().is_some() { "applied to too many arguments" }`.
That refusal is deliberate for the *mask* ("mixing partial application with
implicit insertion is ambiguous"), but the leftover arguments are not partial
application — they are a second, ordinary spine on the result. So the change is:
collect the leftovers, discharge the meta block exactly as today, and hand the
already-zonked `(term, type, level)` plus the leftovers to `apply_explicit`.

**Why after the discharge and not inside the loop.** Inside the mask loop
everything lives in the scratch world where the metas occupy Ψ-indices `[0, n)`
and committed globals are shifted up by `n`; an argument elaborated there has to
be `shift_global(n)`-ed by hand. After `apply_global(&sigma)` the result is back
in the committed world, which is the world `apply_explicit` and every argument it
elaborates already live in. The cost is that a spilled argument cannot drive a
meta solution — `f(a)(b)` where only `b`'s type mentions the type parameter stays
an error. That is the honest shape of the feature (the spilled arguments are
applied to a *result*, whose type is fixed by then) and it is the same behaviour
the explicit spelling `f(a)(b)` has today, so the sugar is exactly the paren
removal it claims to be.

**Failure modes and negative controls.**
- Over-application onto a non-function tail must stay an arity error with the
  callee named. It does: `apply_explicit` reports "`f` is applied to too many
  arguments" at the *offending argument's* span when the type it meets is not a
  Π. Passing `Some(name)` through keeps the callee's name in that message for
  the implicit case too — negative control: `add(1, 2, 3)` and
  `sym(p, q)`-shaped mistakes.
- Under-application is untouched: `apply_implicit` still errors when the mask
  needs an argument and the list is empty, so `nth()` is still "too few".
- A hint for a spilled argument would name the wrong parameter (the parameter
  list ran out), so the spilled call passes `param_offset` such that no hint is
  produced rather than a misleading one.
- No lowering or kernel change: the emitted term is the same `Term::App` spine
  the parenthesized spelling emits, so this cannot make a wrong program check.

## What it assumes from elsewhere
- **[[ih-generalization]]** owns the definition-site fix (elaborator-computed
  Pi motive so `fn nth(xs, i)` can vary `i` across recursion). Assumed here:
  only that it is not landing this round, so curried std fns persist.
- **[[surface-syntax]]** owns call grammar taste. Assumed here: only that
  over-application is currently an arity error, not already sugar.

## Log

- 2026-08-05: LANDED. Two hooks, both in crates/elab/src/lib.rs and neither new machinery. (1) apply_implicit's saturation check no longer refuses leftover arguments: it collects them, discharges the meta block as before, and hands the zonked head to apply_explicit — so nth(t, k) is nth(t)(k). apply_explicit already spilled on its own (it re-reads the callee's type after each argument), so a callee with no implicits needed nothing. (2) DEVIATION, and the one that mattered: elab_self_call had its own exact-arity check, so an *induction hypothesis* could not be over-applied — and the ih is precisely where the curried-return workaround for a varying argument (ih-generalization) puts every call. It now splits the argument list at the declared arity, checks the guard against the first part exactly as before, and applies the rest to the ih's result. Five of the ten collapsed partial-application chains in list-algorithms-exercise are ihs, so without this the feature would have missed its own motivating case. Tests: crates/elab/tests/overapplication.rs, 12 tests — the parenthesized and spilled spellings proved *definitionally equal*, an open element type (the spill happens after the meta discharge, so a spilled argument cannot solve a meta — same as the parenthesized spelling), a checking position at a neutral scrutinee, and five negative controls: over-application onto a non-function tail is still an arity error naming the callee (both the implicit and the explicit path), under-application is still 'too few', a spilled argument of the wrong type is a type error and not an arity error, and a spilled ih still has to descend.
