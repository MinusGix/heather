# One loop combinator

Status: **rounds 1, 2 and 3a merged** (the combinator and its rule; a
`while` outside a `runtime fn` elaborates to it, §5; the reflector read a
twin of the step, §6.1); **stages 3b and 3c built** (one loop node in the
runtime terms, §6.2; one over a span, §6.3); **stages 3d to 3f in review** (a span
loop's state of several words, a loop that only reads its span, and a
statement `if` that joins inside a pass, §6.4; one pointwise pin on every
route, and uniqueness of a well-founded fixpoint, §6.6). The fork round 3
met, decided 2026-11-24, is §6.5, and what is left of the round, 3g and 3h,
follows it (3g's node, lowering and soundness built, §6.8); rounds 4 and 5 (§8) are the rest of the migration. Thread "Rebuild loops on
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

### 6.4 Stage 3d as built: several words, a span only read, a join

Three shapes the ledger's hash-table rows met
(`docs/native/rung2-spans-design.md` §2), each now a loop written in place
over its span:

- **A state of several words beside the span.** The loop's state is
  `Mutated<span, f#State>`, the record of its words. A span function's
  program was built over `Table::none`, so the reflector refused the record
  ("`f#State` has no runtime layout"). The span and `Bytes(n)` generators
  now add the records the walk meets to the program's table
  (`runtime_span_reflect`), but only a loop's state as the elaborator mints
  it (`f#State`, `f#loopK_State`): any other record beside a span is refused
  as before, so `Plain` and `Bytes` as parameters keep their refusals.
  Nothing in the meanings or proofs changed: `FTm::Loop` already carried a
  record of words (`Ty::Carries`), and the table was the one thing fixed.
  The write-out of a `Bytes(n)` function spells a record built and a field
  read as its meaning reduces to, the record's constructor and its
  projections (its table entry's `mk` and `get`); a wrapper around
  `Tm::sem` instead ran the instance's conversion out of fuel, the trap of
  §6.2 (a pass that does not meet the meaning by its arguments is unrolled
  once per pass).
- **The test's fact in a body of several words.** The test bound the words
  by `let`s of its own, so the body's `i` was another local than the
  test's, and `s[i]`'s search could not read `i < s.len()`. Over a span
  with several words the test now reads the state's fields directly.
  `Loop::after`'s type arguments are written too: its result `T` is not
  determined by the state, and a method call in the body
  (`s[i].zero_extend(56)`) was not resolved under an open result.
- **A loop that only reads its `mut self` span** (`Lift::adopt_span`). The
  parser threads only what a loop assigns, so such a span was a capture,
  not a word, and the loop fell back to the lifted form, whose body runs
  hoisted above its test (a read `s[i]` then has no fact). The span is
  carried as the loop's state, unchanged, and rebound to the loop's
  `after` behind it.
- **A statement `if`/`match` that joins inside a pass**
  (`tail_into_join`). The join is `let #stage = match c { … ⇒ Mutated(s,
  c) }; let s = #stage.after; …`, and the span reflector cannot name a span
  through a branch that joins again. In a pass, what follows the join is
  only the rest of the pass down to its next state, so the elaborator
  writes it into each arm (each arm reading its locals straight off its own
  `Mutated(…)`), and each arm ends in its own state, which the reflector
  reads as an `If`. The step's next state is then the `match` itself, and
  its decrease is found under each arm's tests (the closer splits an `if`,
  `issues/while-decrease-through-branches.md`). The rest is copied once per
  arm. **For Minus:** this is the join for loop passes only; a join with
  real code after it in straight-line code still needs `FTm`'s own join
  node, the shared control language of the dogfooding plan §5.3b. Copying
  the tail was chosen for passes because their tail is short (the next
  state, a counter's increment), and it needs no new meaning or proof.
  **Accepted as the stopgap (Minus, 2026-11-24).** Its cost: a pass with
  several joins in sequence copies the rest of the pass at each one, so
  its code grows exponentially in the number of joins in a row (nested
  joins, a join inside an arm, copy only their own arm's tail). The span
  language's join node (dogfooding plan §5.3b) remains the real fix.
- A generator's request budget is ten times a tactic's
  (`GENERATOR_REQUEST_BUDGET`, `crates/elab/src/host.rs`): the insert row,
  three arms of stores, made more than ten thousand requests.

What compiles: the ledger's `Bytes::port_set_put` (the insert as a `while`
over `mut self`, three words, stores in two of three arms) and
`Bytes::port_count_clear_word`; the probes `runtime_span_joins_tests`
(a sum of two words over `Bytes(n)` and over `List<u8>`, a store under an
`if` then code after it, an `if` inside an arm joining words only, and a
negative control whose one arm does not lower the measure). Still refused:
a loop written in place takes only 64-bit words beside its span, so a `u8`
key (`port_count_clear`, `port_find_while`) keeps the loop lifted
(`issues/runtime-repr-narrow-words.md`); `break` and `return` in a `for`.
And `compile-x86` exports a `mut self` function only where its program
marks its span written, so one that only reads its span (the adopted
span's loop, or any `mut self` function that stores nothing) is checked
and published but not exported to x86 (`crates/cli/src/native/verified.rs`).

### 6.5 What is left of round 3, and its fork

Still lifted the old way: loops with an `invariant`, `mut self` loops over
a held record (round 4, `rt_held_loop`), loops whose captures or locals
are not all words, and `Io` loops. And a recursion a user writes as a tail
call still lowers in tail mode, so `Tm::lower_tail`, `Fun::Guarded` and
the companions stay until it moves.

**The fork.** §6 said a user's tail recursion is read as a loop through
`Loop::unique`. Stage 3a found the pin of a `runtime fn` is a conversion,
not a theorem (there is no funext), so a function whose meaning is
`Loop::steps(…)` cannot be pinned to an `f` defined by `decreases`, though
the two agree at every argument. Three ways on:

1. **The elaborator writes a `runtime fn`'s tail recursion as the loop**,
   as it writes a `while` (§6.2): `f`'s body becomes `Loop::steps` over a
   state of its arguments (with several exits, an enum `Go(args) | Out(r)`,
   which the loop node carries as its tag word and slots), and the
   equations a proof cites (`f_unfold`, one per branch) are generated as
   theorems by `Loop::steps_stays` and the step's decrease; `f::induct`
   becomes `Loop::rule` at the step. The pin stays a conversion, callers
   see `f` as it is, and `lower_tail`, `Fun::Guarded`, `rt_loop`'s two
   loop theorems and the measured `FFun` path go.
2. **The pin becomes pointwise**: `Setup::compile` takes `∀ x̄, meaning(x̄)
   = f(x̄)`, proved by `Loop::unique` from `f`'s branch equations. `f`
   stays as written, but every consumer of the pin (callers' tables, the
   span and record publications, the linker's sources) changes from
   conversion to rewriting.
3. Keep tail mode for written recursion and steer ports to `while`. Nothing
   is deleted.

**Decided (Minus, 2026-11-24): none of the three as posed, but the rule
option 2 is a case of, for every function.** The aim is the most elegant
method, easiest to work with and least special-cased.

> The pin is always the function's own unfolding equation, pointwise.
> Whether a self-call becomes a jump or a call is the lowering's choice,
> not the definition's.

1. **`f` is what the user wrote.** `runtime fn` is a marker and never
   changes what `f` is; no source elaborates differently under it, and
   adding a call of itself that is not last does not change how `f` is
   defined.
2. **The reflection reads the body once.** A call of itself in tail
   position is an `Again` leaf of the loop node, any other call of itself
   is a call (the procedure route, `runtime-fn-recursion-design.md` §10),
   and a value returned is `Done`. A `while` (which elaborates to
   `Loop(…).run`) and a tail recursion written by hand reflect to the same
   node: both are a tail-recursive function.
3. **The pin is pointwise everywhere**, `∀ x̄, meaning(x̄) = f(x̄)`
   (`Setup::Pinned`, built for the procedure route), and it is the only
   pin. Its proof depends only on how `f` is defined:
   - where `f`'s body is the reflection's meaning (a function without
     recursion, a `while`), it is `refl`, the check conversion makes today;
   - where `f` is defined by recursion, it is one library theorem proved
     once, **uniqueness of a well-founded fixpoint**: a function that
     satisfies `f`'s unfolding equation, with the measure decreasing at
     each call, is `f`. `Loop::unique` is its case for a loop. Per
     function, the inputs are `f`'s unfolding equation (generated already)
     and the reflection's one-pass meaning (by conversion).
4. **Tail-call elimination is a lowering, proved once** by the loop node's
   pass relation (§6); a call that is not last lowers as a call.

What it removes: the split between a pin by conversion and a pointwise pin;
tail mode (`Tm::lower_tail`), `Fun::Guarded` and the measured `FFun` path;
the distinction between `while` and written recursion in the compiler;
option 1's elaboration that depends on context and on the shape of calls.
What stays: `Loop` and `Loop::rule` as the library for reasoning about
loops (the invariant goes in, the invariant and the exit test come out),
`while` as their sugar, and `f::induct` and unfolding by `refl` on `f` as
written, so proofs about functions are untouched
(`lib/native/runtime/word_map_laws.hthr` among them).

What it costs: the span, laid-record and `Bytes(n)` publications each move
their pin to the pointwise form (`Compile` did in the procedure round); the
expectation, to confirm in the first step, is one congruence lemma per
statement form ("this statement carries along `∀ x̄, f(x̄) = g(x̄)`"), not
one per function. Fixpoint uniqueness proved once. A generated application
of it per recursive function, unmeasured. And every recursive `runtime fn`
needs its unfolding equation present, which
`issues/branch-equations-silent-without-logic.md` shows can go missing
silently today.

Stages, each leaving the gates green:

- **3e.** `Setup::Pinned` the pin of every publication route, proved by
  `refl` throughout: no behaviour changes, and the gates check the
  migration. If the congruences turn out per function rather than per
  statement form, stop here and report: that is the risk this stage
  measures.
- **3f.** Uniqueness of a well-founded fixpoint for measured recursion,
  with `Loop::unique` restated as its case.
- **3g.** The reflector reads a written tail recursion into the loop node,
  its pin by uniqueness. First customers: the ledger's tail calls
  (`Bytes::port_set_insert`, `PortMap::insert_at`, `WordMap::insert_at`);
  regression test: the linked lexer (`crates/linked`, `scripts/linked
  --check`).
- **3h.** Delete `Tm::lower_tail`, `Fun::Guarded`, `rt_loop`'s two loop
  theorems and the measured `FFun` path.

Round 4 (the loop files onto the node) follows as planned, and joins the
same rule: a record or span loop's pin is pointwise like every other.

### 6.6 Stages 3e and 3f as built

**3e: one pin, pointwise, on every route.** The measurement this stage was
for came out as hoped: **one congruence lemma per statement form, none per
function.**

| Route | Pin before | Pin now | Congruence it needs |
|---|---|---|---|
| plain and own-callee (`Setup::compile`) | an equation of curried functions per file (`Setup::at_every`, `lent_every`), or `Setup::Pinned` in a second constructor (`compile_recursive`) | `Setup::Pinned` only, one constructor; `Setup::alike_every` (`Ty::alike_refl`) where the body is the meaning | `Ty::answers_words_alike` (existed); `Setup::agrees_also` derives from it |
| span and `Bytes(n)` (`FFun::compile`) | an equation per rest of file and own span | `FFun::Pinned`: `Ty::AlikeTo` over the words; `FFun::source_alike` by conversion, `FFun::pinned_of_eq` for a function written out over its bytes (its equation read pointwise) | `FTm::answers_alike` (new) |
| laid record (`rt_held`) | at a given environment, own span and record | unchanged: already pointwise | none |
| `Io` programs (`f::bridge`) | per `io` and buffers | unchanged | none |
| measured (`Fun::Guarded`, `FFun::compile_counted`) | its own | unchanged: deleted in 3h | — |

Generic: `Ty::alike_refl`, `Ty::AlikeTo`, `Ty::alike_to_refl`,
`Ty::alike_to_of_eq` (`rt_lower.hthr`). Removed: `Setup::plain_agrees`,
`Setup::compile_recursive`, `Setup::at_every`, `Setup::lent_every`
(`recursive_agrees` is now `Setup::agrees`, `plain_agrees_also`
`Setup::agrees_also`). The kernel's work is the same: the pin's check
still compares the function with its reflection's meaning by conversion,
now under `Ty::Alike`'s binders instead of as an equation of functions.
One diagnostic changed: a wrong claim about a runtime fn's program
(`runtime_sint_tests`' `zext32_is_not_sext`) is still refused by the kernel,
but the elaborator's probe that words a mismatch (it compares the program
spelled by name with the agreement's program spelled out) now runs past its
budget, so the refusal is the kernel's own message; that row expects
`(kernel)` now.

**3f: uniqueness of a well-founded fixpoint** (`loop.hthr`). A recursion
over `A` with measure `m` is a step `F: (a: A) → ((b: A) → m(b) < m(a) →
B) → B`. `fixpoint_unique(m, F, ext, f, g, fe, ge, a): f(a) = g(a)` where
`f` and `g` each satisfy `x(a) = F(a, λ b _ => x(b))` and `ext:
FixpointExt(m, F)` says the step reads its recursion only at its values
(there is no funext, so this is a hypothesis; for a reflection's meaning
it is proved once over the term language, for a function by its `f::ext`
companion). It is the bounded induction `Loop::unique_within` was, over
any step. `Loop::unique` is restated as its case at `Loop::fix`, the
loop's step as a recursion's (`Loop::fix_ext`), with `Loop::run_unfold`
as the loop's equation; `Loop::unique_within` is gone.

**What 3g needs, found on the way.** The loop node of §6.2 is
`Iterate(init, test, body)`: one test, and a stop answers the state. A
tail recursion written by hand has several exits, each answering its own
value, and several calls of itself. Two ways to read it into the node:
(a) a state that is an enum `Go(args) | Out(r)` (the node carries an enum
as its tag word and slots), its test `is Go`, its body the recursion's
body with `Again(ā)` as `Go(ā)` and a returned value as `Out(e)`; or (b)
a node whose body's leaves are `Again(ā)` and `Done(e)`, the shape §6
first drew, with a meaning, lowering and soundness of its own. (a) reuses
everything the node has; its one new piece is the enum, which is not a
type the program declares, so the table needs an entry the generator
makes. (b) is the cleaner node and is new proof work in `rt_lower`.

**Decided (the main session, 2026-11-24, under Minus's principle of the
most elegant method and the least special-casing; for Minus to revisit):
(b), as the one node, not a second one.** (a)'s enum is a type only the
generator knows. A node whose body's leaves are `Again(ā)` and `Done(e)` is
the combinator's own `Pass` shape: a `while`, which elaborates to
`Loop(m, step).run(init)` with a step returning `Again` or `Done`, reflects
to it, and `Iterate` (one test, a stop answering the state) is its special
case. So 3g builds that node in `rt_lower` (meaning, lowering, soundness:
the pass relation of §6, proved once), moves `while` and the span loops
onto it, and 3h deletes `Iterate` with `Tm::lower_tail` and `Fun::Guarded`;
`Iterate` stays only while the migration needs it. Where the proofs come
easiest as a generalisation of `Iterate`'s (a test and a stop as a step of
two leaves), they are written that way. The pin is then `fixpoint_unique` at `f`'s step (from its `f::ext`) and the
meaning's (one-pass unfolding by conversion, `FixpointExt` once over
`Loop::steps` within `Loop::passes()`, by `Loop::steps_stays`).

### 6.7 3g's node: what already exists

Reading `rt_loop.hthr` for the node's proofs: **the pass with `Again` and
`Done` leaves is already built, as tail mode.** `Tm::tail_sem` is a pass's
meaning with its calls of itself (`Call(0, ā)`) answered by a continuation
`again` and every other leaf a value: exactly `Again(ā)` and `Done(e)`.
`Tm::lower_tail` is that pass's lowering (a leaf that goes round moves `ā`
to the loop's next ports with the flag 0, one that leaves moves its value
with the flag 1), and `Tm::tail_sound` its soundness for any `again`: the
pass relation of §6, proved once. What makes it "tail mode" rather than
the node is only where it sits: it is a whole function's shape
(`Fun.shape() = Measured`), and the loop around the pass is justified by
`Fun::Guarded` (the function's `f::ext` and `f::irrel`) instead of by the
pin.

So 3g is mostly moving, not building:

1. **The node is a term.** `Tm::Loop(inits, body)`: the state's words are
   variables `inits`, `body` sees them as its innermost variables, and a
   leaf of `body` that goes round is a new leaf `Again(ā)` (not `Call(0,
   …)`, which inside a function names the function). Its meaning is
   `Loop::steps(Loop::passes(), …)` of the pass `body.tail_sem` with
   `again` the next state: `Step`'s `Next` on `Again`, `Stop` on `Done`
   (the state type then carries the answer: `Step<S>` is generalised to
   `Pass`'s two payloads, `Next(s) | Stop(r)`, as `loop.hthr`'s `Pass`
   already is). Its lowering is `lower_tail` inside a FunctionIR loop
   region, as `Tm::lower_iterate` places `Iterate`'s pass; its soundness
   is `tail_sound` per pass and `Tm::iterate_holds`'s induction on the
   passes, generalised from a test and a stop to the two leaves.
2. **A written tail recursion reflects to `Loop(params, body)`**: its body
   once, a call of itself in tail position an `Again` leaf, so the function
   is plain (`Fun.shape() = Plain`, no `Measured` shape). Its pin is
   `fixpoint_unique` at `f`'s step (`f::ext`) and at the meaning's
   (`Loop::steps` within the measure by `Loop::steps_stays`, its
   `FixpointExt` once over `tail_sem`).
3. **`while`** reflects to the same node (`Step::turn`'s test and stop are
   a `Pass` of two leaves), then `Iterate` goes; then the span language's
   `FTm::Loop` the same way (its `FTm::Again` leaf exists already).
4. **3h**: `Fun.shape()`'s `Measured`, `Fun::Guarded`, `rt_loop`'s two
   loop theorems and the measured `FFun` path are deleted. `lower_tail`
   and `tail_sound` are not deleted but renamed as the node's pass
   (`Tm::lower_pass`, `Tm::pass_sound`): tail mode as a *function's* mode
   is what goes.

The one genuinely new proof is step 1's loop over passes with an answer
leaf, which `iterate_holds` gives the shape of.

**Accepted (Minus, 2026-11-24).** `Tm::lower_tail` and `Tm::tail_sound`
stay, renamed `Tm::lower_pass` and `Tm::pass_sound`, as the node's pass.
What 3h deletes is tail mode as a mode of a whole function: the `Measured`
shape, `Fun::Guarded`, `rt_loop`'s two loop theorems and the measured
`FFun` path.

**What building it found (3g, 2026-11-24).** Four things the plan above
did not see, from reading the code the node has to sit in:

1. **The node's meaning cannot call `tail_sem`.** `Tm::tail_sem` is
   defined over `Tm::sem` (a leaf's value is `Tm::sem` of it), so
   `Tm::sem`'s own case for the node cannot be written through it: the
   two would recurse into each other across modules, and the node's body
   is not a direct subterm of `tail_sem`'s leaves. The term language needs
   what a denotational semantics of loops with labels has: the meaning of
   a term *under the continuation of the innermost loop around it*.
   `Tm::sem_in(t, w, lab)` is that meaning (`Again(res, ā)` answers
   `lab(res, ā's words)`), and `Tm::sem(t, w)` is `t.sem_in(w,
   Tm::no_label(w.tys))`, so every existing statement about `Tm::sem`
   still holds by conversion. A structural recursion may pass a changed
   argument to its recursive call inside a function it hands a combinator
   (a loop's body read under a new label), which is what the node's case
   does. The label is a separate argument, not a field of `World`: a
   term's code (`Tm::ty`) must not depend on it, or every statement about
   a loop body's meaning would be between two types.
2. **Running out of passes cannot answer the state.** `Iterate`'s stop
   answers the state, so a loop out of fuel answers what a stop would, and
   a measure at most the fuel suffices (`Loop::steps_stays`). A `Done(e)`
   leaf answers a value the state does not hold, so the fixpoint pin needs
   the measure *below* the fuel, and a word's `toNat` reaches `2^64 - 1`,
   the passes a FunctionIR loop can count. The measured route meets the
   same edge with one more pass after the loop is exhausted
   (`Fun::meas_tail2`); the node does the same (its meaning's out-of-fuel
   answer is one more pass), which lowers the pass twice. A loop node in a
   pass's second copy is copied again, so code grows exponentially in the
   nesting of answering loops; a `while` (whose stops answer the state)
   needs no second copy.
3. **The first customers are not on the `Tm` route.**
   `Bytes::port_set_insert` is a span function (`FFun`, its tail call
   lowered by `rt_file_loop`'s measured path) and `WordMap::insert_at`
   (and the ports' `WordMap` probes) are laid-record functions whose tail
   pass is `rt_held_loop`'s. A node in `Tm` serves neither: they need the
   node in `FTm`, which is round 4's work (§8). On the `Tm` route, the
   written tail recursions are word functions (`count_down`, `rsum_from`,
   `doubled`, `i64_sum_down` in `lib/_tests/native/runtime/`), and those
   are the node's first customers.
4. **The state is words, at first.** Tail mode's pass moves one word per
   argument and leaves one word; `Iterate` carries a record of words as its
   cells. The node starts with tail mode's shape (each state variable and
   the result held in one word), which is every written tail recursion on
   the `Tm` route; a `while` over a record state moves onto it when the
   pass moves cells, and until then stays on `Iterate`.

### 6.8 3g as built: the node, its lowering and soundness, the pin lemma

**The node** (`rt.hthr`). `Tm::Loop(inits, body)`: the state is the words
of variables `inits`, and `body` sees the state and nothing else (bound as
a function sees its parameters). What a loop reads of its context is a
state word its passes hand on unchanged, so a loop carries no context and
needs none of `Iterate`'s carry. `Tm::Again(res, args)` goes round at the
state the variables `args` hold; it names the loop's result code so that
no term's code depends on the loop around it. The meaning is
`Tm::sem_in(t, w, lab)`, a term under the innermost loop's continuation
(finding 1 of §6.7); `Tm::sem` is it at `Tm::no_label`. A loop's meaning is
`Loop::rounds(Tm::passes(), pass, stuck, words)`, the fuel recursion
(`loop.hthr`), its pass the body under the label `Tm::round(res, again)`,
and past its passes one more pass whose going round answers the state's
first word (finding 2).

**One lowering for a value and a pass.** `Tm::lower` is
`Tm::lower_in(t, w, None, …)`; `Some(PassAt(res, flag, nexts))` lowers a
loop's pass: a leaf is checked at the loop's code and moved out with the
flag 1 (`Tm::leaf_at`), a branch writes the flag and the next words in both
arms (`Tm::branch_at`, tail mode's `tail_branch`), a bound term may not go
round (`Tm::bound_at`), and `Again` moves the state's words with the flag 0
(tail mode's `lower_again`). A value may hold a loop and a loop's leaves
are values, so the two are one recursion, as the meaning is one with its
label. Its soundness is one induction over both modes
(`Tm::lower_in_sound`): a pass leaves the term's meaning under the loop's
label whatever the continuation (`Tm::PassHolds`); a term that goes round
no loop of its own means the same under any label
(`Tm::sem_in_unlabelled`). Tail mode's pass helpers moved from `rt_loop`
to `rt_lower` for it; tail mode itself (`lower_tail`, `tail_sound`) is
untouched and goes with the measured shape in 3h.

**The region** (`Tm::loop_region`): a FunctionIR loop of `Tm::passes()`
passes over the state's words (`Tm::loop_core`), and where it runs out a
second loop node of one pass, so that the extra pass runs on its own
parameters as every pass does and needs no frame reasoning; the answer is
the first output of whichever ran last. Its soundness (`Tm::loop_sound`)
is the pass's (`Tm::core_pass`) and an induction over the passes
(`Tm::rounds_agree`, `Tm::core_runs`), never a measure: the measure
appears only in the pin. Finding 2's cost is the pass lowered twice; a
loop in a loop's pass is lowered twice per copy.

**The pin lemma** (`loop.hthr`, `Loop::rounds_agree`): a run whose every
round, its recursion answered by anything that agrees with `f` below the
measure, is `f`, is `f` wherever the measure is at most the fuel. It is
the fuel side of `fixpoint_unique`, and its one per-function hypothesis is
the shape `Fun::Guarded` has today, which a function's `f::ext` and
`f::irrel` give. A measure that is a word's `toNat` is at most
`Tm::passes()` (`Tm::word_within`).

**Probe** (`lib/_tests/native/runtime/rt_loop_tests.hthr`): `count_down`
written as the node lowers, its meaning is `count_down` by
`Loop::rounds_agree` with the pass from `count_down::ext` and
`count_down::irrel`, and a wrong pass is refused.

**A conversion trap.** Two loops' meanings that differ only in an argument
their passes never read (two labels) ran the kernel out of fuel when
compared by `refl`: it unrolled `Loop::rounds` at its numeral fuel. Each
side's one-step unfolding is its own lemma (`Tm::sem_in_loop`) and the two
are compared through it.

**A written tail recursion on the node (step 2).** A measured recursion
lent nothing, of 64-bit words, is reflected as one node over its
parameters (`Fun::as_node`, `rt_loop.hthr`): its body once, each call of
itself in tail position `Again` (`Tm::again_of`), so the function is plain
and the generator's judgment reads the body as a pass. Its instance
(`runtime_node_instance`, `runtime.hthr`) pins it at each file and word:
the meaning is the node's rounds (`Tm::sem_in_loop`), which are the
function (`Setup::node_means`, `Loop::rounds_agree` at the function's
words) from the node's pass, `Setup::NodePass`, which the generator proves
from `f::ext` and `f::irrel` exactly as it proves `Guarded`, and the
measure a word's `toNat` (`Tm::word_within`). No `f::reflects` is
published for it: the pin is the theorem. `runtime_loop_tests`'
`count_down`, `count_down_odd` and `count_up_to_64` compile this way, and
`examples/x86-native/loop_measure.hthr`'s `triangle` over `count_down`
compiles to certified x86 (217 bytes; the extra pass is a second copy of
the loop's body).

**A second conversion trap, found by the pin.** A cast of a loop's meaning
compared with the meaning itself (`cast(ty, W64, sem(node)) = sem(node)`)
ran the kernel out of fuel: reducing the cast forces the meaning's head,
and the meaning's head is the loop's next pass, at a numeral fuel, without
end. The same comparison between two casts is argument by argument. So the
pin ends in `Ty::cast_self`, spelled so that its statement has the
meaning's own cast, and the kernel never reduces a node's meaning in a pin.
The rule for any proof about a node: never let the kernel reduce
`Tm::sem` of a `Loop` past its head; state the node's meaning through
`Tm::sem_in_loop` and compare loops at `Loop::rounds`.

Still on the measured route (`Fun::Guarded`, tail mode): a recursion lent
a span (the homes it keeps), one whose words are not all 64-bit (records
held in a word, narrower words), and every span, laid-record and `Bytes(n)`
recursion (finding 3). Those are what 3h's deletion waits on.

**Still to do in 3g:** `while` onto the node (step 3), and the node's pin
for words that are not 64-bit (the boundary's casts). What step 3 needs,
found while building step 1:

- *A record state and a record answer.* A `while`'s state is the record
  `f#State` and its answer is that state; the node's state is words and
  its answer one word. Either the pass learns to leave several words (a
  `Done` leaf moving each word of a record, `PassHolds` over a record
  answer), or the reflector spells the state as its fields and the code
  after the loop reads the fields off the node's words. The first keeps
  the node one node; the second keeps the pass one word and needs the
  answer to be a field read, which a `while` whose value is used whole is
  not.
- *The pin is no longer `refl`.* A `while`'s function is written with
  `Loop::steps`, whose stop answers the state, so its meaning equals the
  node's rounds only where the measure bounds the passes; the pin becomes
  `Loop::steps_stays` and `Loop::rounds_agree` meeting at `Loop::run`
  (both are `l.run` within the measure), proved once for a `Step::turn`
  step. That is a theorem per loop the elaborator already has the pieces
  of (`f::loop::runs`).
- Once both are done, `Iterate` and its carry (`Tm::carry`,
  `Tm::iterate_holds`) can go, and the span language's `FTm::Loop` follows
  the same way in round 4.

### 6.9 The pass budget is a proof, not code; a pass of several words

**The principle** (Minus, 2026-11-24; `docs/compilation-vision.md`,
settled principle 13): a runtime check is a proof checked at another time,
and the proof takes primacy. A loop states its termination as an
obligation (a measure that decreases on every pass that goes round),
discharged once; a case the obligation rules out is absurd and emits no
code. A loop counted to a literal bound is a helper that discharges the
obligation for code that wants one, not the primitive.

**Where the counter lives: in the code, all the way down.** §6.8's extra
pass is not only in the node's meaning:

- FunctionIR's `Loop` takes the bound as an input port, binds the passes
  left to `count` on every pass and answers an `exhausted` bit; `LoopRuns`
  recurses on the passes left.
- The allocator emits the count's test and decrement on every pass
  (`loop_zero`, `loop_down`, `loop_stop` in `crates/cli/src/native/allocator.rs`).
- The x86 proofs (`native_compile_structured`, `native_structured_meaning`)
  relate the machine's loop to FunctionIR's evaluator, which is total
  because of the count (`loop_eval(…, remaining, …)`).

The extra pass cannot simply go while the counter stays. With the count at
`2^64 - 1`, `loop_runs_unexhausted` refutes exhaustion only for a measure
below the passes left. A measure that is a 64-bit word's `toNat` reaches
`2^64 - 1`, and its last pass (the one that leaves) is the `2^64`-th.

**Decided** (Minus, 2026-11-24): the primitive changes first, before
`while`, the `FTm` node and 3h. The evidence: `while` onto the node needs
a record answer, which is the multi-word exit in both arms of the
exhaustion branch, and its pin is off by one because of the extra pass
(`rounds(N)` with the extra pass is `Loop::steps(N + 1)`). Every stage
built before the change would be built around the extra pass and then
reworked.

**The change**, in rounds, each leaving the gates green:

- **Round A:** FunctionIR's `Loop` without bound, count and exhausted,
  with its relational meaning, the evaluator and the passes. Today's
  counted users are rewritten onto the helper.
- **Round B:** the native structured layer and its proofs, termination as
  a hypothesis of the lowering's soundness. The `runtime fn` layer
  discharges it from the measure.
- **Round C:** the allocator, the emitter and the decoder (`loop_zero`,
  `loop_down` and `loop_stop` go), the remaining loop producers, and the
  linked assembly regenerated.
- **Round D:** the node without its extra pass, then `while`, the `FTm`
  node and 3h.

What each piece of the change is:

1. FunctionIR's `Loop` loses `bound`, `count` and `exhausted`. Its meaning
   becomes a relation, the loop ends after some number of passes, with no
   case for running out. A run that halts then has its result.
2. Termination becomes a hypothesis of the lowering's soundness, which the
   runtime-fn layer discharges once from the node's measure (the pin
   already has it through `Loop::rounds_agree`). The machine-level proof
   inducts on the passes the relation gives.
3. Today's counted loop becomes a helper: an ordinary state word,
   decremented in the body, whose exit is taken at zero. It discharges the
   obligation for the loops that want a literal bound: the lexer, crypto,
   and the bytes, held and file loops.
4. The node loses its extra pass and its second core. Nested loops stop
   doubling, and a loop's code is its body and the jump back.

The work is several rounds, not one:

- FunctionIR's core, its evaluator and its passes. Most passes lose three
  fields mechanically; the relational meaning and the evaluator are the
  risk.
- The native structured layer and its proofs.
- The allocator, the emitter and the certificate's decoder.
- Every loop producer, then the linked assembly regenerated.

**Round A as built: `Until`, FunctionIR's loop with no bound.** The
counted `Loop` is not changed in place. A second constructor,
`Until(inputs, parameters, body, exit, next, outputs)`, stands beside it.
Its producers move onto it round by round, and `Loop` goes last, so each
round stays green. (`Repeat` was taken: it is a native statement's.)

- *Meaning.* `UntilHolds` is some number of passes (`UntilRuns`, which
  has no case for none) from the inputs to the outputs. The file-threaded
  relation is `UntilRunsOver`.
- *Evaluation.* `until_eval` runs at a fuel that is the meaning's, not the
  code's: `until_passes()`, which is `2^64`. Running out evaluates to the
  state it got to, and that state is never read.
- *Termination.* Running out is not *defined*. `until_defined` is false
  at no fuel, and `defined_over`, which every soundness theorem already
  takes, carries it, so the region's termination is the hypothesis §6.9
  asks for. `until_defined_of_measure` discharges it once: a pass defined
  wherever an invariant holds, and a measure that the passes going round
  lower. `until_word_within` gives that a 64-bit word's `toNat` is within
  the fuel.
- *Not total.* `total_at`, `quiet` and `placeless` are false for `Until`,
  since its termination is never a property of its nodes, and so are their
  lemmas.
- *The passes.* Analyses read its body. Replay, inlining and the
  optimizer's plans take it whole (`Same`, `Stay`), for now.
- *Code.* None in round A: the native layers refused it until round B,
  below. It is spelled with tag 9.
- *A probe split.* `uneven_shallow_exits` (native_compile_tests) sat at the
  kernel's budget. One more constructor in every match tipped it over by
  a sliver, so it is now stage theorems.

**Round B as built: `Until`'s code, with no counter.**

- *The function path* (`function_ir_lower_calls`, the lowering runtime
  functions compile through). The entry moves the inputs into the state's
  registers. A pass is the body, then the exit test (`File::branch_test`);
  leaving moves `next` into the state and jumps out, and going round moves
  them and jumps to the head. There is no counter, no flag and no
  exhausted bit.
  - The machine proof (`until_emits`, `until_rounds`, `until_close_emits`)
    inducts on the passes `∃ n. UntilRunsOver` gives, and the zero case is
    absurd. It is smaller than the counted loop's, and so is each step's
    cost.
  - The planner places the state alone (`File::until_places`).
  - A pass sees the homes the loop carries in (`until_carries`), but no
    homes are carried out yet.
  - Probe `function_ir_until_tests`: a countdown lowers by `refl` to
    `SUB; CMP; JNE` and its jumps, with no counter. A loop whose exit is
    no comparison tests a bit. A stray exit is refused by name.
- *The statement path* (`native_compile_structured` and the layers under
  it). A region holding an `Until` scopes, passes the allocator's check
  (its loop set keyed by its exit id) and is emitted with its machine
  proof (`Target::until_head`, `until_goes`). Termination is the region's
  hypothesis: `StructuredRegion::Ok` takes `until_halts`, which is
  `until_run_defined` from every state.
- *Open: a statement cannot hold an `Until` yet.* A statement's meaning
  (`Stmt::denote`'s `Compute`) has no hypothesis and no meaning for a loop
  that does not end. `native_compile_correct` is cited by the ELF theorem
  whose call the Rust emitter writes. So `scopes` refuses an `Until`
  (`until_free`) until one of these is chosen:
  - (a) `Compute` gets a meaning that can stop short (fuel, or a `Cut`).
  - (b) The compile's correctness and the ELF theorem take a termination
    hypothesis, which changes the call Rust writes.
  - (c) A termination check the compile decides.

  The native tools (`native_build`) are the counted loop's only
  statement-level producer, so this decides how they leave `Loop` in
  round C.
- *Decided (Minus, 2026-11-25): every loop carries its measure.* The
  obligation is on the primitive (vision principle 13). The FunctionIR
  `Until`, at both levels, and the runtime node `Tm::Loop` each carry a
  measure over their state. Its decrease on every pass that goes round is
  proved where the loop is built: by evaluation where the measure and the
  step are closed, by a carried proof otherwise.
  - Definedness is then generic at every level: `until_halts` follows from
    the carried measure by `until_defined_of_measure`. Neither the
    compile's correctness nor the ELF theorem takes a hypothesis, and the
    Rust emitter's call does not change.
  - Not (a): pure regions stay total, and a program that runs forever has
    the statement-level `Repeat`. Not (b): that puts the obligation on the
    program rather than on the loop that needs it.
  - The counted loop is the helper. A counter word is its own measure, so
    `native_build`'s loops move onto `Until` with a counter in their state,
    and `Loop` goes as planned.
  - Round D: the node carries its measure, and `rt_lower_defined` stays
    generic.
- *Rust.* The region printer reads tag 9. The allocator does not, since no
  statement reaches it with an `Until`.

**Round C as built so far.**

- *The measure.* `Until` carried a seventh field, `measure`: the position
  of the parameter it falls on. Round D removes it (below).
- *The counted check* (`function_ir_counted`). A pass that counts is
  `Compose(work, Dataflow(leaf))`, where `work` writes no part of the
  counter and the leaf is exactly `counted_nodes(p, q, exit, t)`:
  `t := 1; q := p - t; t := 0; t := (q = t); exit := exit | t`. `p` is the
  parameter at `measure` (none before it) and `q` the next word there.
  `StructuredRegion::counts` decides it by evaluation, and
  `counts_halts` turns the verdict into `until_halts`. The measure is the
  counter less one, so a loop entered at zero wraps and still ends within
  `until_passes()`. The file-threaded `until_run_defined_of_measure`
  carries it.
- *Statements.* `scopes` asks `until_counted` where it asked
  `until_free`. `ok_of_scoped` proves an `Until`'s ending from the check,
  and needs no hypothesis. A `BitOr` of two clean bits is clean
  (`Scope::clean`), so the counted exit bit scopes.
- *A layout fix.* Round B's statement code jumped back to the head
  conditionally. A `Jcc` lands only ahead (`item_lands`), so no program
  holding one laid out. It went unnoticed because `scopes` refused every
  such statement. The code now jumps ahead to the jump back, as the
  counted `Loop`'s does, and `counted_compiles` checks a whole source.
- *`native_build`.* `Passes` lowers to a counted `Until` over the counter,
  `ran_out` and the state, behind a test of its bound. Each pass sets
  `ran_out` to the negation of `stop`, so the last pass leaves it 1
  exactly where the passes ran out.
- *A measure is any function of the state, carried by the proof* (was:
  a parameter's position; see the decision below).
- *The runtime producers: held for a decision.* Every runtime producer of
  `Loop` is already replaced or deleted in round D:
  - `Iterate` goes when `while` reflects to the node;
  - the node carries its measure;
  - `rt_loop`'s fuel and measured theorems and the measured `FFun` path go
    in 3h;
  - `FTm::Loop` goes onto the `FTm` node.

  So porting them in round C builds them twice, whether onto a derived
  `counted_loop` or directly onto measure-carrying `Until`s. The direct
  route cannot reach `Iterate`, which has no measure, nor the node, until
  round D gives it one. The order proposed instead:
  - round C closes with what is built;
  - round D's node lowers straight to an `Until` carrying the node's
    measure (the direct route, for the one producer that stays);
  - deleting `Loop`, the allocator's `loop_zero`, `loop_down` and
    `loop_stop`, and regenerating linked follow 3h, once nothing makes a
    `Loop`.

  **Decided (Minus, 2026-11-25):** this order. Round C is closed as built
  (9720631). The counted `Loop` stays in use by the runtime producers
  until 3h.

**Round D, stage 1: the measure is evidence, not code.**

*Decided (Minus, 2026-11-25).*

- *The node's measure is a ghost.* It is the pin's `m`: the function's
  `decreases` expression, any function of the state words whose value is a
  word's `toNat` (`Setup::NodePass`, `node_means`). The compiled loop
  computes nothing for it (vision principle 13).
- *Its decrease comes from the pin.* A node goes round only from tail
  position, so a pass that goes round at `xs` answers exactly `k(ys)`.
  Suppose it went round with `m(ys) >= m(xs)`. Two continuations that agree
  below `m` and differ at `ys` would then give `f(xs)` two values, and
  every answer type has two. So `NodePass` alone says each pass that goes
  round lowers `m`. One structural lemma about `Tm::loop_body` carries this
  (it is `k` at the state the pass names, or does not read `k`), and the
  generator owes nothing new. `rt_lower_defined` stays generic: the node's
  case takes the pin's `m` and `NodePass`.
- *`Until` has no `measure` field.* A measure is evidence, so it belongs
  with the loop's definedness proof, which takes any measure function and
  invariant already (`until_defined_of_measure`). Each producer supplies
  its own:
  - the node, from the pin;
  - the counted check, from the counter its leaf names: in
    `q := p - t`, `p` is the counter and `q` its next word, found in the
    parameters and the next words by walking them together.

  So every loop carries its measure, and no field means something only
  sometimes.
- *The node's meaning.* With no count and no extra pass it is
  `Loop::rounds(2^64, pass, stuck, xs)`, where `stuck` reads the state
  back. One `Until` matches it pass for pass, an exhausted `Until` leaving
  the state as `stuck` does, so the code's eval needs no measure. Only its
  definedness does.

**Round D, stage 1 as built: the node is one `Until`.**

- *Meaning.* `Tm::Loop`'s meaning is `Loop::rounds(Tm::rounds(), pass,
  read_words, xs)`, where `Tm::rounds()` is `2^64`, as many as
  `until_passes()`. Past its rounds it answers its state read back, as an
  exhausted `Until` leaves it. The pin is `Loop::rounds_agree_below`: rounds
  above the measure are the function, whatever answers past them. A word's
  `toNat` is below `2^64`, so the extra pass and its off-by-one are gone.
- *Code.* `Tm::loop_region` is one `Until` (`Tm::node_core`). It has no
  bound word and no count, no exhausted bit, no second core and no branch
  after it. The answer is the first output, the state's first word whether
  the passes left or ran out (`Tm::extra_end`). The id layout is kept: the
  bound's and count's ids are simply unused.
- *Soundness.* `Tm::until_round_of` and `Tm::until_rounds_agree` are the
  `Until` forms of the pass and the fuel recursion. `Tm::node_pass` is one
  pass for any continuation, and `Tm::core_pass` is its instance at the
  rounds. `Tm::loop_sound_at` lost its second core and its branch.
- *Definedness.*
  - The node's pass is `quiet`: `Tm::quiet_in` reads the `Until`'s pass.
  - Its ending is a new premise of `Tm::DefinedHolds`, `Tm::Ends`. It is
    structural: a term with no node owes nothing (`Tm::ends_free`, by
    evaluation of `Tm::nodeless`). A node owes `Tm::NodeEnds`: a measure of
    its words, at most a word's `toNat`, under which its pass is pinned
    (`Tm::NodePass`, moved down from `Setup::NodePass`).
  - `Tm::node_defined` turns that into `until_defined` by
    `until_defined_of_measure`. A pass that goes round to `ys` answers its
    continuation at `ys` (`Tm::node_pass`). Were `ys` not below the
    measure, two continuations that agree with the pinned function below
    it but answer `0` and `1` there would give the function two values.
- *The generator.* A measured recursion compiled as a node gets
  `f::ends` (`Setup::node_ends_of`): its measure, the generator's `word_within`
  bound, and its pass pinned at the world of the empty file, all from what
  it already builds for the pin (`runtime_node_measure`,
  `runtime_node_pass`). `Compile::ranked_code`, `total_code`, `test_code`
  and `walked_code` take `Compile::LoopsEnd`. A program's part reads a
  callee's `f::ends`, its root's from the assembly, or `Compile::ends_free`.
- *Probes.* `runtime_depth_tests`: `rsum_nodes`, a leveled recursion
  calling the node `down_node`, is defined at no premise past its levels,
  and agrees there. `down_node`'s code is quiet, and `ends_free` cannot
  stand in for its measure (negative control).

**Built: a pass that answers several words** (step 3's first half, kept
as small as the extra pass allows).

- *The answer.* A node's answer is a `Ty::Answer`: a 64-bit word, or a
  record of 64-bit words with one field at least. It is held at its ids
  (`Ty::ids`), and the leaf moves them to the first of the next words.
  Every other next word gets a copy of the first id (`Tm::fill`), so a
  branch's arms both write each one.
- *The statement.* The pass's statement is in words: `Tm::leaves`, at
  `Ty::result_words`, takes the first `res.span` next words.
- *The extra pass.* The meaning's extra pass, going round, answers the
  state read as the answer (`Ty::read_words`, moved into `rt`). An
  answer's words read back as itself (`Ty::answer_round`), so the extra
  pass's end is the state's first words (`Tm::extra_end`). An enum is not
  an answer yet: a word past its last tag reads back as another
  constructor.
- *Tail mode.* Tail mode keeps its one-word `Tm::leave` and `Tm::out`
  until 3h deletes it.
- *The loop's exit.* After the loop, the answer is still moved out in one
  word (`lower_loop_at` checks `res.check_one_word`). Generalizing that
  exit is a move of each word in both of the exhaustion branch's arms, and
  (2) deletes that branch; so it waits on (2)'s order.

**What `while` onto the node still needs** (step 3's second half):

- *Its state as words.* A `while` is an expression,
  `Loop::steps(Loop::passes(), λ s => Step::turn(c, λ h => next, s), init)`,
  over a state of any code, and its test and next state may read the
  function's context. The node's body sees only its state (`Tm::inside`).
  So the reflector spells the record state's fields, and every context
  variable the loop reads, as one-word state words. It re-indexes the test
  and the next state onto them: the test's two arms become `Again` of the
  next fields and the read-only words, and `Make` of the fields. A context
  word that is not one 64-bit word keeps the loop on `Iterate` until the
  node's state widens.
- *Its pin.* The pin is a rewrite inside f's body at the loop's position,
  not `refl`. That position is where `Iterate`'s meaning is `Loop::steps`
  itself. `Loop::steps_stays` and `Loop::rounds_agree` meet at `Loop::run`,
  from `f::loop::runs`, under the congruence of the context around the loop.

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
   *Status (2026-11-24):* 3a–3f built; 3g's node, its lowering and
   soundness, its pin lemma, and written tail recursion over 64-bit words
   on it are built (§6.8). Left: `while` onto the node (a record state),
   the node's pin at words that are not 64-bit, then 3h. The span and
   laid-record recursions (the ledger's tail calls) need the node in `FTm`,
   which is round 4.
4. **The other four loop files onto it** (`rt_file_loop`, `rt_held_loop`,
   `rt_bytes_loop`, and `rt_io_loop` via `Io::iterate`), with the shared
   `FTm`/`ETm` core of the dogfooding plan §5.3b; delete their companions.
5. **The ledger's loop rows** as the first customers: Fibonacci with two
   loop words, a read-only `for` over `Bytes(n)`, `return` in a `for`, and
   an `if` that stores and then joins.

Rounds 2 to 4 change the language surface's meaning and the generator, so
each is a PR for Minus to review.
