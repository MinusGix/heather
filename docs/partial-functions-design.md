# Partial functions as coinductive computations

Status: **round 1 (the library) implemented**, 2026-10-31, after Minus
agreed with the proposal and with dropping the decimal formatter as the
customer. Issue `issues/partial-functions-coinductive.md` (item 5, part 2,
of the fundamental-improvements memo of 2026-10-31). Written on master
`c7f5472`. §8 says what landed and where it differs from §4.3; rounds 2
and 3 (§6) are not built.

## 0. The answer in one page

- **The direction is sound, and most of it is already built.** `CoTree`,
  `CoTree::iter`, `Eutt`, and the bridge to the fuelled `Program`s
  (`docs/coitree-design.md` §§1–8) are everything a partial function needs
  except one combinator, `CoTree::rec`. That combinator is about thirty lines
  over `iter`, and the probe in §3 shows that it checks, that its unfolding
  laws hold by `refl`, and that running it at a literal costs time linear in
  the number of calls.
- **The issue's "done when" picks the wrong customer.** The decimal
  formatter is *total*. Its fuel is a termination witness, there because
  `decreases` over `match n.leb(9)` gets no unfolding equation
  (`issues/unfolding-computed-scrutinee.md`). Making it `partial` would turn
  its `List` into a computation that every caller then has to bind or
  discharge, and that is worse than the fuel. Termination-witness fuel
  belongs to measures (`while … decreases`, sequencing R3). `partial` is for
  functions whose divergence is real (§1).
- **Recommended meaning:** `partial fn f(x: A) → B` declares
  `f : A → CoTree<B>(E)`, with `E = Events::none()` for a pure function, so
  the type says the result may not arrive. The body is elaborated with each
  self-call as an event, and `f` is `CoTree::rec` of that body. When every
  self-call is a tail call, `f` is `CoTree::iter` of a pass over the
  arguments instead. That is the shape the native compiler's `Repeat`
  already denotes, through `iter_refines` (§4).
- **What proofs get, proved once in the library and never per function:**
  observation-level unfolding laws (by `refl`), `Returns(t, b)` as "after
  some count of silent steps, `t` returns `b`", a fixpoint-induction rule
  for partial correctness, a measure rule for termination, and
  `Partial::get(t, h)` to go back to a total value when termination is
  proved. Fuel appears only inside proofs, as the count in `Returns`.
- **Three rounds** (§6): the library combinator and its rules (no
  dependencies), then the `partial fn` surface (after the sequencing
  carrier, R2/R3), then partial `runtime fn` loops (after
  `runtime-fn-default-setup`, R5). I suggest the kernel model's
  `Tm::whnf(fuel)` as the first real customer instead of the decimal
  formatter, because its divergence is genuine and its soundness proof is
  already a fixpoint induction (§5).

## 1. Three kinds of fuel in the library

Every `fn`/`theorem` signature that takes a `fuel` argument, on `c7f5472`,
falls into one of three kinds. They want different fixes.

| Kind | What the fuel means | Examples | The fix |
|---|---|---|---|
| **Termination witness** | The function is total; fuel is a cheap way past the termination checker, and theorems carry a `n <= fuel` side condition | `decimal_digits` (`lib/std/text/decimal.hthr`), `Nat::ldiv_fuel`, `isqrt_fuel`, `pow_sq_fuel`, `width_fuel` (`nat.hthr`), `Format::pick` (a bounded search, `b + fuel = span`) | measures and their unfolding equations: `issues/unfolding-computed-scrutinee.md`, `while … decreases` (sequencing R3) |
| **Real divergence** | The computation may not stop; theorems are partial correctness, true at every fuel | `Tm::whnf`, `Tm::read`, `Tm::strip` (`lib/kernel_model/`), every `while … fuel` loop the sequencing surface will write without a measure | **`partial fn`**: this note |
| **Budget** | The bound is part of the meaning | tactic search depth (`mono`, `cast`, `norm_num`), `Steps(R, fuel)` in `relation.hthr`, `Series::settle` (stops summing at the cap, sound at any cap) | stays as it is (the issue says so too) |

The native semantics is a fourth case that is already solved: `Source::denote`
is a `Program` (`lib/native/native_source.hthr`), a fuel-indexed family whose
statements (`Program::Refines`, `Produces`, `Diverges`) quantify the fuel
away. No native theorem statement mentions fuel today.

So `partial` has a narrower job than the memo item gives it. It removes fuel
from the second row, and gives `while` loops with no measure a meaning that
is not "`Exhausted` after `n` passes".

## 2. What exists

From `docs/coitree-design.md` and the code under `lib/std/itree/`:

- `CoTree<R>(E)`, codata over the kernel's `M`, with observations `Obs` and
  the observation-seeded style that works without η (§2 there).
- `CoTree::iter(E, body, a)`: a loop with no fuel, every pass guarded by one
  `CTau` (`coitree.hthr:129`).
- `Bisim` and `Eutt` with the monad laws, and `Eutt` with counted tau drops.
- `CoTree::program(t)`, which turns a tree into a `Program` through its
  approximations, plus `iter_refines`/`iter_refined` and
  `bind_refines`/`bind_refined` against `Program::iter`/`Program::bind`
  (`coitree_bridge.hthr`).
- On the finite side, `ITree::rec`/`ITree::mrec` (`itree.hthr`):
  recursion as an event family `D`, interpreted with fuel.

**What is missing** is the coinductive `rec`. The codata surface cannot
write it as a direct corecursion: a non-tail self-call sits under a `bind`,
which is not a constructor, so it is not a guarded call
(`docs/codata-elaborator-design.md` §5.2; `issues/codata-nested-guards.md`
covers only calls under a *second constructor*, which this is not). The
standard way around that is Coq's ITrees `interp_mrec`: run a loop whose
state is the pending tree, and at a call replace the call with the body
bound to the call's continuation. `iter` supplies the guard, so nothing new
is needed from the surface.

## 3. The probe

`partial_probe.hthr` (in the project files, `partial-fns/`) checks on
`c7f5472` with `heather check --cache --expectations`:

```heather
fn CoTree::rec_vis<R>(D: Events, E: Events, body: (d: D.Cmd) → CoTree<D.Resp(d)>(Events::sum(D, E)),
    c: Events::sum(D, E).Cmd) → (Events::sum(D, E).Resp(c) → CoTree<R>(Events::sum(D, E)))
    → CoTree<Step<CoTree<R>(Events::sum(D, E)), R>>(E)
{
    match c {
        Inl(d) => λ k => CRet(Continue(CoTree::bind<D.Resp(d), R>(Events::sum(D, E), body(d), k))),
        Inr(e) => λ k => CVis(e, λ x => CRet(Continue(k(x)))),
    }
}
fn CoTree::rec_step<R>(D: Events, E: Events, body: …, o: Obs<R>(Events::sum(D, E))) → … {
    match o {
        ORet(r) => CRet(Break(r)),
        OTau(s) => CRet(Continue(s)),
        OVis(c, k) => CoTree::rec_vis(D, E, body, c, k),
    }
}
fn CoTree::mrec<R>(D: Events, E: Events, body: …, t: CoTree<R>(Events::sum(D, E))) → CoTree<R>(E) {
    CoTree::iter(E, λ s => CoTree::rec_step(D, E, body, CoTree::obs(Events::sum(D, E), s)), t)
}
fn CoTree::rec(D: Events, E: Events, body: …, d: D.Cmd) → CoTree<D.Resp(d)>(E) {
    CoTree::mrec(D, E, body, body(d))
}
```

The signature is the finite `ITree::rec`'s with `CoTree` for `ITree` and no
fuel, so `D` can be a sum (mutual partial functions come free) and the
answer type can depend on the call (`D.Resp(d)`).

What it shows:

- **Unfolding at open arguments, by `refl`.** `obs(mrec(CRet(r))) = ORet(r)`,
  `obs(mrec(CTau(s))) = OTau(mrec(s))`, and the one that matters,
  `obs(mrec(CVis(Inl(d), k))) = OTau(mrec(bind(body(d), k)))`: a call is one
  silent step to the body bound to its continuation. A command of `E` passes
  through with a silent step after its answer. That holds per observation of
  the child, not as one equation, because there is no η for codata, which is
  the usual `coitree` situation.
- **Convergence at a literal, by a count and `refl`.** A Collatz step counter
  written as a `partial` body (`collatz(6)` returns `8`) is a theorem
  `after(100, collatz(6)) = ORet(8)` by `refl`, and a wrong value is refused
  by the kernel (`NotConvertible`). The count is an upper bound, and a larger
  one is harmless, because `after` stops at the first settled node.
- **Cost is linear in the number of calls.** Measured in kernel steps
  (`--timings`), a plain `iter` loop costs about 60–80 steps per pass, a
  direct corecursion about 28 per `CTau`, and doubling the depth doubles the
  steps up to 320 passes. The non-tail `rec`, the tail-recursive `rec`
  (identity continuation) and the hand-written `iter` loop grow together:
  the loop is 15–20% cheaper at ten calls and 3% cheaper at thirty-five, so
  the pending-tree state adds a constant per call and no superlinear term. (The Collatz runs themselves do grow superlinearly, but that cost is
  `Nat::div`, which is linear in the *value* in the kernel: `9232 / 2` alone
  is over the 2^20 step budget. It is unrelated to partiality.)

## 4. The design

### 4.1 Meaning

`partial fn f(x: A) → B { … }` declares `f : A → CoTree<B>(Events::none())`.
A library alias, `Partial<B>`, names that type (Capretta's delay monad). A
`partial` function with effects, such as a runtime loop reading until EOF,
declares `f : A → CoTree<B>(E)` for its events `E`.

The type shows the partiality. That is the deliberate difference from Lean
4's `partial`, which keeps `A → B`, needs `Inhabited B`, and makes `f` opaque
so that nothing can be proved about it. Heather wants specifications for
these functions, and an honest type is what makes them stateable.

### 4.2 Elaboration

1. The body is elaborated over the carrier `CoTree(Events::sum(Calls(A, B), E))`,
   where `Calls(A, B) = Events(A, λ _ => B)`. Each self-call `f(e)` is a bind
   point, `CVis(Inl(e), λ r => …)`. That is the sequencing surface's carrier
   scope (`docs/sequencing-surface-design.md` §2) with `CoTree` as the
   carrier, so `partial` waits for R2 (`Bind<M>` over `Type → Type`) and adds
   no binding machinery of its own. In v1 a self-call is written
   `let r <- f(e);`. An implicit bind at a bare `f(e)` can follow.
2. **The tail case.** When every self-call is in tail position, `f` is
   `CoTree::iter` of a pass over the arguments (`Continue(args)` at a call,
   `Break(v)` at a return). That is exactly `Program::iter`'s shape and the
   native `Repeat`'s, so `iter_refines` carries it to the `Program` world
   with no new proof. A `while … ` loop with no measure is this case.
3. **The general case.** `f(x) := CoTree::rec(Calls(A, B), E, f#body, x)`.
   Mutual `partial` functions use a sum of call families for `D`.
4. **Refusals, each with its reason:** a `partial fn` whose body never calls
   itself (it should be a plain `fn`); a self-call outside a bind position;
   using `f(x)` where a `B` is expected ("`f` is partial: bind it with `<-`,
   or use `Partial::get` with a termination proof").

### 4.3 What proofs see

The rules are generic in `rec` and `iter`, proved once in the library, and
every `partial fn` uses them. Nothing is generated per function except the
name of its body, which `f_unfold` exposes.

- **Unfolding.** `f_unfold : obs(f(x)) = …` at each observation, by `refl`
  (the probe's three laws). Up to `Eutt` the useful form is
  `f(x) ≈ bind(f#body(x), f)` with calls answered by `f`. That form needs the
  eutt `bind` congruence (`issues/coitree-eutt-bind-cong.md`), which becomes
  a prerequisite.
- **`CoTree::Returns(t, b)`**: a record of a count `n` and
  `after(n, t) = ORet(b)`. This is the only place a natural number appears,
  and it is existential. Literal runs prove it with a count and `refl`.
- **Partial correctness (fixpoint induction).** `CoTree::rec_induct`: if
  `P(d, r)` holds of every `r` the body returns for `d`, assuming every call
  it makes answers within `P`, then `Returns(rec(d), r) → P(d, r)`. The proof
  is an induction on the count, inside the library. This is the rule
  Isabelle's `partial_function` and Lean's `partial_fixpoint` both give, and
  it is the shape `Tm::whnf_sound` already has (§5).
- **Termination by a measure.** `CoTree::rec_returns`: if every call the
  body makes at `d` has a smaller measure, then `rec(d)` returns something.
  This is where a measure meets a partial function.
- **Back to a total value.** `Partial::get(t, h: Halts(t)) → B` reads the
  value off the count. So a function can be written `partial` first and
  given a total face once termination is proved. That is the Bove–Capretta
  route, derived rather than built in, with `get(f(x), …)` playing the role
  of the domain-predicate version.
- **Against the fuelled programs.** `CoTree::rec_refines`/`rec_refined`
  against `Program::rec`, as `iter_refines` is against `Program::iter`.
  Native needs this only for non-tail recursion (§4.4).

The proofs use the observation style `coitree.hthr` already uses: a convoy
on `obs(t)`, and `j` along `obs_bind_at`. A user proving partial correctness
with `rec_induct` never sees that style.

### 4.4 Native

A partial `runtime fn` loop (read until EOF, serve forever) is the tail case
over `Events::linux()`: `CoTree::iter` of a pass. Its agreement with the
compiled `Source` goes through `iter_refines` to `Program::iter`, which is
what `Stmt::denote` gives a `Repeat` (`native_source.hthr:271`). So the
native half adds nothing to `Source` or its proofs. It does need the
`runtime fn` generator and the default setup first (R5,
`issues/runtime-fn-default-setup.md`), and it should be scoped to tail
recursion: a non-tail partial function at run time needs a call stack, which
belongs with `nh-heap` and the stack-frame work.

### 4.5 Alternatives considered

- **Lean 4 `partial`** (opaque, `Inhabited`): nothing can be proved, so it
  fails the "specifications without fuel" goal outright.
- **Least fixpoints in a CCPO** (Lean `partial_fixpoint`, Isabelle
  `partial_function (option)`/`(tailrec)`): this is the right *user*
  experience, with equations plus a fixpoint induction rule. But the
  definition is a classical limit, and Heather computes with its kernel, so
  `refl` at a literal and `write-elf`'s evaluation would both be lost. The
  coinductive definition gives the same two rules and still computes.
- **Bove–Capretta domain predicates** as the primary form: these compute,
  but every caller has to pass a domain proof even to state a partial
  correctness fact, and each function needs its own generated inductive.
  §4.3's `get` gives this face whenever it is wanted.
- **Keep fuel, hide it in a `Program`**: this already works for native. For
  pure code, though, a `Program` is a family of trees, not a value with
  observations, and the bridge already lets `CoTree` statements be carried
  over to it.

## 5. A first customer: the kernel model's evaluator

`Tm::whnf(fuel) : Tm → Option<Tm>` (`lib/kernel_model/kernel_reduction.hthr:268`)
is written in open-recursion style: `Tm::step(ev, t)` takes the recursive
evaluator as `ev`, and `whnf(Succ(g)) = step(whnf(g))`. Untyped weak-head
reduction can genuinely diverge, so this fuel is real divergence (§1). Its
soundness proof (`kernel_runs.hthr:241`) is induction on the fuel with
`step_sound(ev, ih)`, which maps `Sound(ev)` to `Sound(step(ev))`. That is
`rec_induct` with `P = Reduces`, almost literally. Restating it as
`Returns(whnf(t), v) → t.Reduces(v)` is a small round once `rec_induct`
exists. It also tests the one real wrinkle: `step` is written against
`ev : Tm → Option<Tm>`, and the partial version wants it against the
`CoTree` carrier. That is a customer for the `Bind<M>` class
(`issues/higher-kinded-classes.md`), or `step` gets rewritten over calls as
events.

## 6. Rounds and the issue's revision

1. **`partial-rec-library`** (no dependencies): add `CoTree::mrec`/`rec`
   to `coitree_bridge.hthr` or a new `coitree_rec.hthr`, along with the
   unfolding laws, `Returns`, `rec_induct`, the measure rule, `Partial::get`
   and `rec_refines`. Its customer is the kernel model's `whnf` restated
   without fuel (§5). Prerequisite for the eutt-level unfolding:
   `coitree-eutt-bind-cong`.
   *Done, 2026-10-31, except `rec_refines` (§8).*
2. **`partial fn` surface** (after sequencing R2/R3): elaboration (§4.2) with
   the tail case to `iter`, the refusals, and `f_unfold`.
3. **Partial `runtime fn` loops** (after R5): tail case only, through
   `iter_refines`.

**Change to the issue's "done when"** (agreed by Minus, 2026-10-31): drop the decimal formatter,
because its fuel is a termination witness and belongs to
`unfolding-computed-scrutinee` and sequencing R3. Replace it with "a
function whose divergence is real (the kernel model's `whnf`) is restated
with no fuel in its statements, its soundness proved by fixpoint induction;
and a `partial` runtime loop compiles under the default setup."

## 7. Risks

- **No η** means every unfolding law is per observation. The library hides
  that behind `rec_induct` and `Returns`. A user who unfolds by hand meets
  the convoy style.
- **Export** to Lean/Rocq refuses codata (`issues/export-codata-m.md`), so
  partial functions do not export until that does.
- **Kernel evaluation** of a long run is linear in calls (§3), but each
  `refl` at a literal needs a count large enough. A `Returns` helper that
  searches for the count, so the user never writes one, is a small tactic
  once `norm_num`-style deciders exist.

## 8. Round 1 as built

`lib/std/itree/coitree_rec.hthr`, with its customer in
`lib/kernel_model/kernel_whnf.hthr`. No kernel or elaborator change was
needed. Every theorem below is proved once, over any `D`, `E` and body.

- **The loop**: `CoTree::rec_vis`, `rec_step`, `mrec` and `rec`, which is
  §3's probe. `Events::calls(A, B)` names a function's calls.
- **Unfolding**: `CoTree::mrec_obs(o)` is what `mrec(t)` observes when `t`
  observes `o`, which holds by `δβ`. `mrec_at` rewrites `obs(t)`, and
  `mrec_ret`, `mrec_tau` and `mrec_call` hold by `refl` at open arguments.
  `mrec_cmd_settled` says a command of `E` is a settled node.
- **`Returns(E, t, r)`** is a record of a `count` and
  `after(count, t) = ORet(r)`.
- **Partial correctness** (`rec_sound`, called `rec_induct` in §4.3). The
  body's obligation is `CoTree::Safe(D, E, P, body(d), P(d))`. That is a
  computed type indexed by a step count (`SafeObs`), not an inductive
  family, because a family indexed by a tree is not constructor-headed
  (`docs/inductive-indexed-lowering.md` §1), and the itree library already
  reads relations off observations this way. Users never see the count:
  `safe_ret`, `safe_tau` and `safe_call` build the obligation one
  constructor at a time, and `safe_bind` composes it. The proof is an
  induction on `Returns`' count, which matches on the pending tree's
  observation.
- **Sequencing**: `mrec_bisim` says bisimilar pending trees return the same
  values after the same count. `mrec_bind` says a pending tree that returns
  `a`, followed by a continuation that returns `r` from `a`, returns `r`.
  The call case meets `bind(bind(body(d), k'), k)` against
  `bind(body(d), λ x. bind(k'(x), k))`, and `bind_assoc` with `mrec_bisim`
  closes it, so no `Eutt` was needed.
- **Termination** (`rec_total`, called `rec_returns` in §4.3). The body's
  obligation is `CoTree::Reaches(D, E, P, Ok, body(d), P(d))` with
  `Ok(d2) = measure(d2) < measure(d)`: within some depth, every path returns
  within `P(d)`, calling only allowed arguments. The proof is an induction
  on a bound above the measure, with `mrec_reaches` inside it, and
  `mrec_bind` for each call.
- **Back to a total value**: `CoTree::get(E, t, h)` reads the value off the
  tree, running it for the count in `h`. `get_eq` and `get_returns` state
  what it gives. In the probes, `sum_value(4) = 10` holds by `refl` through
  `rec_total`'s witness.
- **Not built**: `rec_refines` against `Program::rec`, which is
  `issues/coitree-rec-program-bridge.md` (§4.4: only non-tail native
  recursion needs it), and the eutt-level `f(x) ≈ bind(body(x), f)`, which
  waits on `coitree-eutt-bind-cong`.

**The customer.** `Tm::step_co` is `Tm::step` with each recursive
reduction as a call. `Option` is gone, because it only ever stood for
running out of fuel. `Tm::whnf_co(t)` is `CoTree::rec` of `step_co`, and
`Tm::whnf_co_sound` (every value it returns is a reduct) is `rec_sound`
with `P = Reduces`. The per-case lemmas are `whnf_sound`'s, with `safe_call`
in place of `ih`. The fuelled `Tm::whnf` stays, because `kernel_runs.hthr`'s
folds read it.

**Tests.** `lib/_tests/std/itree/coitree_rec_tests.hthr` covers:
- a tail-recursive unbounded search and a non-tail sum, run at literals by a
  count and `refl`;
- the unfolding law at an open call;
- the search's result, proved by `rec_sound`;
- a function that only calls itself, proved never to return by `rec_sound`
  with `False` as the invariant;
- the sum, proved total by its measure, with its value read back by `get`;
- a wrong value and a short count as `expect-error` controls.

`lib/_tests/kernel_model/kernel_whnf_tests.hthr` covers:
- β, ι and a stuck application, at literals;
- soundness used at a literal run;
- `Ω` still running after any count tried;
- a wrong normal form and a short count, both refused.

One thing the probes surfaced: a body whose `match` is on a computed
scrutinee (`big(n)`) needs that scrutinee as a parameter of a helper
(`search_at(n, b)`) before a proof can case on it. That is
`issues/unfolding-computed-scrutinee.md` again, met from the proof side.
