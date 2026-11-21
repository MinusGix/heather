# One loop combinator

Status: **rounds 1, 2 and 3a merged** (the combinator and its rule; a
`while` outside a `runtime fn` elaborates to it, §5; the reflector read a
twin of the step, §6.1); **stage 3b in review** (one loop node in the
runtime terms, `while` and counted `for` over words written as
`Loop::steps`, §6.2). Stage 3c and rounds 4 and 5 (§8) are the rest of the
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
state instead of calling an `ih` with five arguments. Each conjunct of the
next state's invariant is a `bv_omega` inside an anonymous pair: the goal
there is `b.next.lo <= b.next.hi` over the pass's payload, which `bv_omega`
reads through the value the step built (docs/tactics/bv-omega-design.md
§4), so no conjunct needs its type written out and no midpoint lemma is
named.

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

### 6.1 Round 3 in stages

Every counted `for` over words and every `mut self` loop in the library is
in a `runtime fn` (the SHA-256 modules, the ports, the runtime tests); the
one ordinary function with one is `induct_word_loop_tests`. So they move
with round 3, not before it, and round 3 is staged so that each stage is
a PR that leaves the native gates green:

- **3a. The reflector reads the combinator; the elaborator stops lifting.**
  In a `runtime fn` too, a `while`, a counted `for` and a `mut self` loop
  elaborate to `Loop(…).run` (§5). The reflector reads
  `Loop(m, f#step).run(init)` as today's measured `Fun`: the state's
  fields are its words, an `Again(Lower(next := S(ā), …))` leaf is a
  call of itself on `ā`, a `Done(e)` leaf is `e`. What `rt_loop` needs of
  a measured function, `Fun::Guarded`, is proved once in the library from
  `Loop::run_unfold` and the `less` each `Again` carries, where today
  each function proves it from its own generated `#ext`/`#irrel`. The
  lifting half of `loops.rs` and its companion family go. Tail mode stays
  for this stage.
- **3b. One loop node, agreement as a relation.** `Tm` gains the loop
  node of §6; its lowering is the body, the moves and the flag; its
  soundness is the pass relation, proved once over `Function::run` with
  `Loop::rule`. `Tm::lower_tail`, `Fun::Guarded` and `rt_loop`'s two loop
  theorems go; a recursion a user writes is read as a loop through
  `Loop::unique`.
- **3c.** The other four loop files onto the node (round 4 above).

**3a as built (2026-11-20, replaced by 3b).** A `runtime fn`'s `while` over one
`u64` local with `u64` captures and no stated fact elaborates to the
combinator (`loops.rs`, `lift_while_runtime`): `f#loop(c̄, v̄)` is
`f#loop#of(c̄, v̄).run(f#State(v̄))`. Reading the step itself turned out not
to work: matching on `step(s)`'s result against the reflected tail-mode
body is a commuting conversion, which the kernel does not do. So the
elaborator also writes the step's *twin*, the same tests with the two
leaves as functions (`again(c̄, v̄′)`, `done(r)`), and a theorem
`f#loop#elim`: `match step(c̄, State(v̄)) { Again(b) => again(c̄, b.next.v̄),
Done(r) => done(r) } = twin(c̄, v̄, again, done)`, by `split_all; all_goals
{ refl }`. The reflector reads the twin (`rt_reflect_loop`: `again` is the
self-call, `done` the answer), and the generator
(`runtime_loop_instance`) proves `Fun::Guarded` by
`Fun::guarded_of_loop` (`rt_loop.hthr`), every obligation a conversion but
the step's, which is the loop's own `elim`. No `#ext`, `#irrel` or
companion is involved. Probes: `runtime_while_combinator_tests`. Still
lifted: a state of two locals, a fact-carrying loop, `mut self` loops and
counted `for`s.

`port_fib` and `port_bits` (`runtime_ports_tests`) are refused today because
their state, two words, is a record with no runtime layout: the lifted loop
is a function that returns it. Stage 3a alone keeps that (its loop is still a
measured `Fun`), so those two need either a two-word result for the loop's
function or stage 3b, whose node keeps the state in the loop's homes and
never makes it a value. 3b is the one that fixes them for good.

### 6.2 Stage 3b as built: the loop node

What 3a taught: the kernel will not commute a `match` on a step's result
into the step's own tests, and a `runtime fn`'s instance is pinned by
*conversion* (`Setup::compile`'s `pinned` is an equation of curried
functions, and there is no funext to prove one any other way). So the
loop's meaning in a `runtime fn` must be a term that the reflected node's
meaning converts to, with no theorem in between. 3b is that, end to end,
and the 3a twin path (`::twin`, `#elim`, `rt_reflect_loop`,
`runtime_loop_instance`, `Fun::guarded_of_loop`) is deleted with it.

- **A proof-free iteration in the library** (`loop.hthr`).
  `Step<S> { Next(s), Stop(s) }`, `Loop::steps(fuel, step: S → Step<S>,
  s) → S` (`steps(0, s) = s`; `steps(k + 1, s) = match step(s) {
  Next(t) => steps(k, t), Stop(r) => r }`), and `Step::turn(go, next, s)`,
  the `match h: go` a `while` writes: `Next(next(h))` while `go` holds,
  else `Stop(s)`. Running out answers the state it got to, so no value is
  invented. `Loop::steps_stays` proves the iteration is `Loop::run`
  wherever the measure is at most the fuel, the step agrees with the
  loop's, and a stop stays where it is (`Step::turn_stays`).
- **The fuel is a name.** `Loop::passes() = 2^64 - 1`, the most a 64-bit
  count reaches, so every measure that is a word's `toNat` is below it
  (`rt::Tm::word_within`). As a numeral, two loops compared at their
  `Loop::steps` unrolled pass by pass wherever a field read forced the
  state; as a name they compare by their arguments. The reflector refuses
  a loop given any other fuel.
- **The elaborator writes the loop where it stands** (`loops.rs`,
  `lift_steps`). A `runtime fn`'s `while` or counted `for` whose locals and
  captures are words, with no facts, no receiver and a word's `toNat` as
  measure, becomes

  ```text
  loop::Loop::steps(loop::Loop::passes(), λ (t: S) => loop::Step::turn(
      { let v̄ = t.v̄; c₁ && c₂ … }, λ _ => { let v̄ = t.v̄; body; S(v̄′) }, t), S(v̄₀))
  ```

  where `S` is the one local's type or the generated record `f#State` (a
  counted `for` adds its count as a field, `i < hi` its test and `i + 1`
  its next value). Nothing about the loop is a function of the program.
  Beside it the elaborator writes the loop's reasoning, checked the
  ordinary way: `f::loop::step`, a `Pass` whose decrease is found
  (`bv_omega`; a body that does not lower the measure is refused there,
  "this pass of the loop must decrease the measure"), `f::loop::of`, its
  `Loop`, `f::loop::same` (the pass read without proofs is the written
  `Step::turn`, by `split_all` and `refl`), and the theorem a proof about
  `f` rewrites by, `f::loop::runs(c̄, s): Loop::steps(passes, turn, s) =
  of(c̄).run(s)`, one application of `Loop::steps_stays`. With several
  loops, `f::loop1_loop::runs`, ….
- **One node in the runtime terms.** `Tm::Iterate(init, test, body)`
  (`rt.hthr`): the state is variable `init` (a word or a record of words);
  `test` (a bit) and `body` (the next state) see it as variable 0. Its
  meaning is `Loop::steps(Loop::passes(), λ s => Step::turn(test, λ _ =>
  body, s), init)`, so the pin of a function with loops in it is still a
  conversion and the instance is a plain function's. The reflector
  (`rt_reflect.hthr`, `rt_steps`) reads exactly that shape.
- **Its lowering is a FunctionIR loop region** (`rt_lower.hthr`,
  `Tm::lower_iterate`): the state and the context are the region's
  parameters (a record as its fields, an enum as its tag word and slots,
  `Ty::cells`; never a buffer), a pass is the test, a branch that moves the body's value
  (or the state itself, once the test fails) to fresh ports, and the exit
  bit, the test's bit exclusive-ored with 1 (the emitter has no 1-bit
  compare). The region is given `Loop::passes()` passes, the meaning's
  fuel. Its soundness, `Tm::iterate_holds`, is by induction on the passes
  and never mentions a measure: the measure appears only in
  `Loop::steps_stays`, about Heather terms.

**A conversion trap found on the way.** Reading a record field after a
symbolic loop ran the kernel out of fuel: the meaning side stalled at
`Ty::cast`'s `Nat::equation`, a global older than `loop`, and the δ-lazy
rule "unfold the newer side" unrolled the program's `Loop::steps` instead.
The casts now decide on rt's own copy, `Ty::nat_equation`, newer than
`loop`, so the cast unfolds first. A constant the meaning waits on should be
newer than what the program's side unfolds into.

**What compiles.** `port_fib` and `port_bits` (`runtime_ports_tests`) are
accepted: a state of two words is a record held in the loop's homes, never
a function's result. `drop_to` and `port_bits` compile to certified x86 and
pass a native test. `port_fib` does not reach x86 yet: a FunctionIR loop
pass sees only its parameters, so the region carries every word of the
context, and fib's ten words leave the planner no register for the next
state. Carrying only the variables the test and body read needs a lemma
that a term's meaning ignores an unread variable
(`issues/iterate-carries-whole-context.md`).

Still lifted the old way: loops with facts, `mut self` loops, loops whose
locals are not all words, and the other four loop files (3c, §6.3).

### 6.3 Stage 3c as built: loops over a span

**One node for a computation over a span.** `FTm::Loop(init, test, body,
rest)` (`rt_file.hthr`): the state is the span and variable `init`'s words,
`Mutated<span, S>`; `test` (a bit) reads the words as variable 0 and the
span as it is; `body` is a computation over the span ending in the next
words; `rest` runs from the span and words the loop leaves. Its meaning is
`FTm::rest_of(…, FTm::iterated(…), env)`, where `iterated` is
`Loop::steps(Loop::passes(), FTm::turn(…), Mutated(own, init))` and every
read of a loop's state goes through `Loop::after(m, k) := k(m.after,
m.value)`. Its lowering is a FunctionIR loop region carrying only the
variables the test and body read (`Tm::carry`, `FTm::loop_keep`), and its
soundness (`FTm::loop_case_sound`, `rt_file_lower.hthr`) is proved once by
induction on the passes. Over a `Bytes(n)` the meaning is `FTm::over`'s
`Loop` arm, and the two meanings agree by `Loop::steps_map` (a loop seen
through a map that commutes with its pass is the other loop), proved once
in `loop.hthr`.

**The elaborator writes the loop where it stands.** In a `runtime fn` whose
receiver is its span (`List<u8>` or `Bytes(n)`), a `while` or counted `for`
whose other locals and captures are words, with no `invariant`, is
`Loop::steps(passes, λ t => Loop::after(t, λ span v => Step::turn(test, λ h
=> { body; Mutated(span, S(v̄′)) }, t)), Mutated(s, S(v̄)))`
(`Lift::lift_steps_over`), and the code after it reads the span as
`#loop.after` and a word as `#loop.value` (or `.value.x`). A loop in its
body is written first (`Lift::nested`). Its step is `Pass::of_turn` of the
loop's one test, so that `f::loop::same` is one lemma,
`Pass::step_of_turn`: the body's found proofs (`s[i] := 0` finds `i <
s.len()`) read the test's equation, which a `split_all` of the goal cannot
abstract.

**The reflector reads it as one node** (`rt_file_loop`,
`rt_file_reflect.hthr`): `Loop::steps(…).after` is a link of the span's
chain, its start the span inside `Mutated(span, v̄)`; the test and body are
reflected under the words, the body as a walk of its own over the span its
pass is handed (`FileKnown::inside`). Two things a loop's body needs from
outside it:

- A byte of an enclosing walk's span (the outer loop's span in insertion
  sort, read as `key` before the inner loop) is a variable bound before the
  loop: the plan scans a loop link's pass at the state after it, and the
  body reads that state through `FileKnown.outer`.
- A loop carries 64-bit words only (`Ty::Carries`), so the words its test
  and body make only of what is bound outside it are bound before it
  (`rt_file_invariants`): `key.zero_extend(56)` is carried, not the byte.

**Written out over a `Bytes(n)`.** The function of a `Bytes(n)` is also
written out as a function of its bytes (`SpanWriting::written`,
`runtime.hthr`). Its `Loop` arm spells the pass as `FTm::turn` does
(`Loop::after`, the test through `Ty::cast`, the body through
`FTm::recast`), and the write-out's agreement with its code is compared at
an abstract function, as a measured function's is: compared at the
function itself, its run's words spelled two ways are compared by running
the loop, once per pass of `Loop::passes()`.

**What compiles.** Insertion sort over a `List<u8>` span is two nested
loop nodes and runs by `refl`; `Bytes::clear` is one.

**Still lifted the old way:** loops with an `invariant` (their facts would
be fields of the state, forgotten by `Loop::steps_map`), `mut self` loops
over a held record (SHA-256, `Sched`, `Tally`), loops whose locals are not
all words, and `Io` loops. A recursion written as a tail call still lowers
in tail mode, so `lower_tail`, `Fun::Guarded` and the companions stay until
those move.

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
