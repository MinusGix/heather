# One loop combinator

Status: **round 1 built** (the combinator, its rule, a case principle for a
step, probes); **round 2 in review** (a `while` outside a `runtime fn`
elaborates to the combinator, §5). Rounds 3 to 5 (§8) are the rest of the
migration. Thread "Rebuild loops on
one combinator", 2026-11-19, from the dogfooding review
(`docs/native/dogfooding-plan.md`, PR #804).

## 1. Why

A `while` or a counted `for` today lifts to a function of its own that calls
itself last (`f#run`, or `T::f_loop` at a `mut self` receiver), and that
function brings a family with it: `#ext`, `#irrel`, `_unfold`, `#induct`,
`#keepsK` for each invariant fact, `#found_N` for each lifted search, the
branch equations `::step`/`::done`. The native side reads the lifted
function back as a loop: the body is lowered in **tail mode**
(`Tm::lower_tail`), and the loop's soundness needs `Fun::Guarded`, proved per
function from `#ext` and `#irrel`.

Agreement between a function and its code is an *equation between total
functions*, checked by conversion. It must therefore hold at every state,
including states where the loop's facts are false. That one choice is why
`FFun::rounds`, `FFun::when(ok, …, idle)` decide guards, re-finding facts at
each state (`FFun::all_true`, `FFun::falls_over`) and the `∥Empty∥` bridge
exist, and why a caller of a loop that takes facts has no route at all
(`issues/span-caller-of-fact-taking-loop.md`).

All of it is written five times: `rt_loop`, `rt_file_loop`, `rt_io_loop`,
`rt_held_loop`, `rt_bytes_loop`, about 4,800 lines and 118 theorems, plus
about 7,000 lines of the elaborator (`loops.rs`, the loop half of
`measure.rs`, the loop shapes of `branch_equations.rs` and
`function_induction.rs`).

The Io layer was already the other shape: `Io::iterate` of a step
`A → Io → Step<A, B>`, with soundness proved once as a relation kept by each
pass (`Io::iterate_rel`). This design makes every loop that shape.

## 2. The combinator (`lib/std/core/loop.hthr`)

```
record Lower<S>(m: S → Nat, s: S) { next: S, less: ∥m(next) < m(s)∥ }
inductive Pass<S, R>(m: S → Nat, s: S) { Again(next: Lower<S>(m, s)), Done(r: R) }
record Loop<S, R> { measure: S → Nat, step: (s: S) → Pass<S, R>(measure, s) }

fn Loop::run(self l, s: S) → R
theorem Loop::run_unfold(l, s): l.run(s) = match l.step(s) { Again(b) => l.run(b.next), Done(r) => r }
theorem Loop::rule(l, I, Q, keeps: (s) → I(s) → Pass::Keeps(…, l.step(s), I, Q), s, start: I(s)): Q(l.run(s))
theorem Loop::unique(l, g, same: (s) → g(s) = match l.step(s) { … g(b.next) … }, s): g(s) = l.run(s)
```

- **The state is whatever the loop needs, facts included.** A loop whose
  body reads `s[j - 1]` under `0 < j` and keeps `j <= i` has
  `record Hole(n, i) { s: Bytes(n), j: u64, kept: ∥j <= i∥ }` as its state.
  Its step is a total function *of states where the fact holds*: there is no
  state where it fails, so no junk branch, no decide guard, no re-finding.
  A fact is squashed: nothing at run time, and two states that differ only
  in a proof are one state.
- **The decrease is the step's.** `Again` carries `∥m(next) < m(s)∥`, found
  where the step is written, under the tests that lead to it: exactly where
  today's `on ?decN` obligations are found. So `Loop::run` is defined once
  for every step, and nothing is generated per loop to make it total.
- **`run` is structural on a bound** (`Loop::within`, at most `k` passes,
  `k` above the measure), and `Loop::within_irrel` says the bound does not
  matter. That is §1 of `docs/language/recursion/decreases-unfolding-design.md`
  done once by hand in the library instead of generated per function. (A
  `decreases m(s)` definition was tried first: the unfolding generator
  cannot lift an obligation that names a constructor field of a
  parameterised inductive, so it would have needed a generator change for
  no gain.) It evaluates by `refl`: `count_up(60, 0) = 246`, the binary
  search, and the whole insertion sort over `Bytes(5)` all do.
- **What comes out of a loop is its answer `R`.** For an elaborated `while`
  that is the final state, with the invariant as a field and the exit test
  as one more: *the invariant goes in, the invariant and the exit test come
  out*, as values the code after the loop reads, not as `#keepsK` theorems.
  The probe's outer sort reads the inner loop's `h.kept` to store at `h.j`.

## 3. The cost of giving up `f::induct`: none measured

The worry was that a lifted loop's free `decreases` and `f::induct` would be
lost. They are replaced by two things proved once:

- `Loop::rule` is the induction. A proof about a loop states the invariant
  and proves `keeps`: one pass from a state where it holds keeps it or
  leaves at an answer with the postcondition.
- `keeps` is a case split on the step, and the step is an ordinary
  non-recursive function. `induct f(…)` now accepts one (§4) and gives one
  arm per way the step can go, named as for a recursive function
  (`True::True`, `True::False`, `False`), with the step's equation for that
  arm. No induction hypothesis: the rule supplies it.

The probe re-proves `examples/binary-search`'s `lower_bound_splits` this way
(`lib/_tests/std/core/loop_tests.hthr`). `Range::search_keeps` is the
example's `lower_bound_in_splits` arm for arm; the headline is one
application of `Loop::rule`. Each arm returns the invariant at the next
state instead of calling an `ih` with five arguments. It came out a few
lines longer, for two reasons that are gaps in `bv_omega`, not in the rule:
it does not see the midpoint's bounds through `r.lo`/`r.hi` (the example's
`midpoint_from`/`midpoint_below` are named in the arms), and a conjunct of
an anonymous pair is not a goal it spells (each is given a `let` with its
type).

What is genuinely different: the invariant is a named predicate on the state
(`Range::Splits`) rather than a theorem's hypotheses, and the postcondition
cannot mention the start state unless the invariant carries it. Both are
the usual Hoare-logic shape and read better.

## 4. Elaborator changes in round 1

- **`induct` on a function that does not recur** (`declarations.rs`
  `cases_only`, `function_induction.rs`): its principle has a motive of no
  arguments and one case per branch equation, no hypotheses. Built on
  demand, in generated mode, reading the equations the function was
  declared with. It is what replaces `f::induct` for loops, and it is
  useful on its own for any function that is a tree of tests.
- **A fact bound by `let` is released for a search** (`checking.rs`
  `release_squashed_facts`): `let kept = h.kept;` makes `∥j <= i∥` available
  to `bv_omega` and to a default argument's search, as a parameter's fact
  already was. A loop state's facts are fields, so this is how a step reads
  them.

## 5. Elaborating `while` and `for` (round 2)

`while c invariant P decreases m { body }` over the locals `v̄` it assigns,
with captures `c̄` (as today):

- `record f#State(c̄ the types need) { v̄, held: ∥P∥ }`: one field per
  assigned local, one per invariant conjunct (and the free facts of
  §23.6 of the sequencing doc that the body reads).
- `fn f#step(c̄, #s: f#State) → Pass<f#State, f#Out>(f#measure(c̄), #s)`:
  `let v̄ = #s.v̄; let held = #s.held;` then `match h: decide_bit<c>()
  { True => { body; Again(Lower(next := f#State(v̄', found), less := found)) },
  False => Done(f#Out(v̄, #s.held, exit := squash(h))) }`. The facts and the
  decrease are found at the `Again` by the default search, under the arm's
  tests, as `on ?decN` and `#keepsK` obligations are found today.
- The loop itself is `Loop(measure := …, step := λ s => f#step(c̄, s)).run(init)`
  inline in `f`'s body. A nested loop is the same expression inside the
  outer step. **Nothing is lifted** except the step (which could be a `λ`;
  a named step is what `induct f#step(…)` and the native reflector read).
- `for i in lo..hi` is the `while` with measure `(hi - i).toNat()`.
  `return v` inside the body is `Done(Return(v))` with `f#Out` a two-way
  sum, which is what the dogfooding probe 6 (`memchr`) needs.
- A `for x in xs` over a list stays the `foldl` it is: a fold is already a
  loop with a structural measure, and its proofs are list induction.

**As built (round 2).** The names are `f::State` and `f::step` (minted
`f#State`/`f#step`, designated under the loop's own name with every member
of the step's family, so a proof writes `induct f::step(s)` and
`f::step::True`); with several loops in one function they are
`f::loopK_State`/`f::loopK_step`, numbered in order. The state's fields are the
assigned locals and then one per invariant conjunct and free fact. The
decrease and the facts at `Again` are found by the measure closer
(`omega`, then `bv_omega` over words); when it fails, the error says that
this pass must decrease the measure, at the `decreases` clause. A module
with a `while` imports `loop`. A loop's type arguments are not inferred
from a `Loop(…)` a proof writes: it writes `Loop<f::State, f::State>(…)`.
Still lifted in round 2: a `mut self` method's loops, a counted `for` over
words, and every loop of a `runtime fn` (its reflector reads the lifted
form until round 3).

What disappears: `Lift::lift_while`, `lift_while_method`, `lift_counted`
and their method-receiver forms; the measure lowering of the lifted loops
and their `#ext`/`#irrel`/`_unfold`/`#induct`/`#keepsK`/`#found_N` family;
`at_result`/`Held`/`found_at_entry`. What stays: the parser's threading of
assigned locals (`\0loop`, `\0proj`), the capture oracle (`BinderTys`),
`subst_shared`.

## 6. Native: one loop node, agreement as a relation (rounds 3 and 4)

Reflection sees `Loop(…).run(init)` as one node, `Loop(init, step)` in the
shared term language, the step's body with two kinds of leaves, `Again(ā)`
and `Done(e)`. Its lowering is `ELoop::loop_stmt`'s shape: the body, the
moves of `ā` back to the state's homes, and the flag the `Repeat` tests.
**There is no tail mode**: the step is lowered like any other term whose
value is a two-constructor sum.

Soundness is a relation, proved once per evaluator:

> From a machine state that holds `s` at the loop's homes, one pass reaches
> a machine state that holds `next` (on `Again`) or the answer (on `Done`).

and the loop theorem is `Loop::rule` with the invariant *"the machine holds
the state"*: induction on the measure, which `Again` carries. Since the
loop's facts are fields of a state the step never sees without them, the
relation is only ever asked at states where they hold. `FFun::rounds`,
`FFun::when`, `Fun::Guarded`, the decide guards and the re-finding all go.
A caller of a loop with facts (`issues/span-caller-of-fact-taking-loop.md`)
stops being a separate problem: it passes the facts in the initial state,
which it has to prove anyway.

A recursion that calls itself last, written as recursion
(`examples/binary-search`'s `lower_bound_in`), is read as a loop by
`Loop::unique` from the branch equations the function already has: the
probe's `count_down_is_loop` is `Down::step_agrees` (an `induct` with one
equation per arm) and one application of `Loop::unique`. So the tail-mode
lowering can go even for recursion.

`Io::iterate` stays for loops with no measure, in `Partial`; a measured loop
in an effectful program is `Io::iterate` of the step with `Lower` forgotten,
equal to `CRet(run(s))` by one lemma from `Loop::rule`.

## 7. Bootstrapping

Minus's fear: a bug that infects the next version. The loop's meaning is
three library declarations and a rule the kernel checks; the elaborator's
output for a `while` is an ordinary term the kernel checks; agreement is
proved once per evaluator, by the kernel. Nothing in the elaborator or the
reflector is trusted, so a wrong elaboration is a refused declaration, not a
wrong compiler.

## 8. Rounds

1. **Built (this round).** `lib/std/core/loop.hthr`; `induct` on a
   non-recursive function; `let`-bound facts released; probes
   `lib/_tests/std/core/loop_tests.hthr` (count up, binary search with its
   theorem by the rule, tail recursion as a loop, negative controls) and
   `lib/_tests/native/runtime/bytes_loop_combinator_tests.hthr` (the
   insertion sort over `Bytes(n)`, both loops, facts in the state).
2. **`while` and counted `for` elaborate to the combinator** in ordinary
   functions (§5); re-elaborate the library; port the library's proofs that
   cite `f::run`, `f::step`, `R::f_loop`, `#keepsK` to `Loop::rule`.
3. **One loop node in the shared term language** and its relation
   (§6) over `Function::run`; `runtime fn` reflection reads `Loop(…).run`;
   delete `Tm::lower_tail`, `Fun::Guarded`, `rt_loop`'s two loop theorems.
4. **The other four loop files onto it** (`rt_file_loop`, `rt_held_loop`,
   `rt_bytes_loop`, and `rt_io_loop` via `Io::iterate`), with the shared
   `FTm`/`ETm` core of the dogfooding plan §5.3b; delete their companions.
5. **The ledger's loop rows** as the first customers: Fibonacci with two
   loop words, a read-only `for` over `Bytes(n)`, `return` in a `for`, and
   an `if` that stores and then joins.

Rounds 2 to 4 change the language surface's meaning and the generator, so
each is a PR for Minus to review.
