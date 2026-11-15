# Facts on demand: a first prototype

Status: prototype landed 2026-11-01. It extends `docs/compilation-vision.md`
§6.2 ("facts on demand: dispatch methods, and checks as searches") and does
not re-derive it. Tracking issue: [facts-on-demand](../../issues/facts-on-demand.md);
the second fact, `Unique` over `rt` (§7), is [unique-fact](../../issues/unique-fact.md).

§6.2 asks for four things. A fact is an open class with several producers.
Producers are lazy and run cheapest first, with the generic search last. A
check is a search with a budget, and a failed search skips the optimization.
The compiler sees only a proof. This round built each of them from what the
elaborator already had, plus two small additions, and ran them end to end on
a small language whose compiler drops bounds checks.

| piece | where | new or reused |
|---|---|---|
| a fact and its producers | evidence rules (`docs/library/positivity-evidence-design.md` §9) | reused |
| a producer that searches | **search rules** (§3) | new, one function in `crates/elab/src/resolve.rs` |
| asking from a generator, and hearing "none" | the **`Synth`** host request, `request` (§4) | new request; library in `lib/std/tactic/fact_request.hthr` |
| a budget | `budgeted` (§4) | library |
| a compiler proved once over any facts | proof-carrying sites (§5) | pattern; `lib/lang/facts/checked_reads.hthr` |
| the first fact, `InBounds` | `lib/lang/facts/in_bounds.hthr`, `read_facts.hthr` | library |
| the second fact, `Unique` over `rt` (§7) | `lib/lang/facts/unique.hthr`, `write_facts.hthr` | library, plus `rt`'s byte read and write |

## 1. What a fact is

A fact is a **proposition**, and its producers are the **evidence rules** that
conclude it. §6.2 called it an open class, and the open part is what matters.

A class instance is a dictionary, and its registry is coherent: one instance
per key, because a program can observe which dictionary it was handed. A fact
is different, because nothing observes which proof of it was found.
Section 6.2 already says this ("opaque to the compiler"). So a fact needs no
coherence, and its producers must be able to overlap: the range analysis, a
user's lemma and a search all conclude `InBounds(len, bounds, e)` for the
same arguments. The class registry refuses that by design. The evidence-rule
registry was built for it: it is keyed by the conclusion's relation, several
rules about one relation coexist, and each one is a kernel-gated trial
(`issues/infer-proposition-evidence.md`).

So the prototype adds no `fact` declaration form. A fact is a `fn … → Type`
(`InBounds`), and a producer is an `evidence theorem` concluding it. Whether
a marker for facts is wanted later is in §8.

Q2 of the vision note, whether a fact is about the function or about the
code, gets a concrete answer here. `InBounds(len, bounds, e)` is about one
read of the code, and it is stated as mathematics about that read's index:
for every argument list in the box, `e.eval(args) < len`.

## 2. The order producers run in

A request for a fact runs the search a `:= infer` parameter runs at a
proposition. The first three steps are unchanged:

1. **Locals**, up to conversion.
2. **Computation**: a goal that reduces to `True` within a small fuel.
3. **Plain rules**, each premise searched by the same procedure. These are
   evidence rules whose every parameter is `{…}` or `:= infer`.
4. **Search rules** (new, §3), after every plain rule.
5. Then, outside the registry, the **requester's own fallbacks**, each run
   under the requester's budget (§4).

Steps 1 to 4 are the fact's producers, registered by whoever can produce the
fact. Step 5 belongs to whoever asks for the fact. That splits Q8 of the
vision note ("who pays for search") in two. A producer that needs a search
says so once, for every request. Any extra search is the compiler's choice,
made at its own budget.

## 3. Search rules

A **search rule** is an evidence rule with a premise that has a default, so
that the premise runs something:

```heather
evidence theorem Fits::by_omega({i: Nat}, {n: Nat}, h: i < n := omega): Fits(i, n) { h }
```

This is the `instance(f) NoAlias(f, i) := by search(…)` line of §6.2,
written with machinery that already existed. Two changes in
`crates/elab/src/resolve.rs` made it work:

- **A search rule is built as a call.** A candidate used to be the bare
  rule name in checking position. That fills implicits and solver
  parameters, but a parameter default fills only at a call
  (`docs/language/named-arguments-design.md` §9.6). So a rule with a defaulted
  parameter is elaborated as `rule()`. Its tactic premise then runs as a
  default does: in the goal's context, made hygienic, so `omega` reads the
  caller's hypotheses (`from_local` in `lib/_tests/std/tactic/fact_request_tests.hthr`).
- **Search rules go last.** The rules about a relation are tried in
  canonical order, plain rules first and search rules after them. A goal
  that a cheap producer answers never pays for a search (`doubled` in the
  same tests: the plain rule answers, and its premise reaches the search
  rule).

Whether a rule is a search rule is read off its declaration's parameter
table (`Elaborator::is_search_rule`). Nothing new is stored in a module
image, so the image format is unchanged.

**Termination.** Paterson's condition still applies to every `:= infer`
premise. A defaulted premise is not searched through rules, so it is not
measured. Its tactic runs once per trial. A default that itself runs `infer`
or `positivity` would search again; resolution's depth cap (`MAX_DEPTH`) is
what bounds that, as it bounds a registry whose decrease check failed.

**Cost.** `docs/library/positivity-evidence-design.md` §6 declined omega inside
`infer`, because `infer` runs invisibly at every call site. A search rule
does not reopen that question. It is opt-in for each relation, so only goals
of that relation pay, and the author who registers it chooses the cost, as
the author of a parameter default `h: 0 < n := omega` does. Nothing
registers a search rule about `Nat::Lt`.

**The cheap check is a search rule too, for now.** The range analysis's
premise, `e.hi(bounds) < len`, is a comparison of numbers that evaluates to
`True` at a closed read. It is the cheapest producer of all. It cannot be a
plain `:= infer` premise: it mentions all three of the conclusion's variables
plus `hi` and `<`, so Paterson's condition refuses it as not smaller. It is
written `h: e.hi(bounds) < len := trivial` instead, a search rule whose
"search" is one evaluation. Search rules about one relation run in canonical
name order, so two of them cannot yet say which one is cheaper. §8 lists
the ways out.

## 4. Asking for a fact, and hearing "none"

An optimization that finds no proof must be skipped, not fail. Neither
`:= infer` nor a parameter default can do that: both stop elaboration when
they fail. So the ask happens in a generator, which is where a compiler
already runs (`generate`, `docs/metaprogramming/host-elaboration-interface-design.md` §19).

**`Synth(goal: Handle) → Checked<Handle>`** is a new host request
(`lib/std/tactic/tactic.hthr`, `Elaborator::synth_request` in
`crates/elab/src/host.rs`). It runs `resolve_goal` at the type the handle
stands for, in the handle's scope. That is the whole search: locals, derived
table, instances, computation, plain rules and search rules. A failure
comes back as a refusal that carries the search's trace, and the refused
search leaves nothing behind (`SearchMark`). The type must mention no
unsolved hole, because the search's trials are the elaborator's, and they
know nothing about a run's holes.

`lib/std/tactic/fact_request.hthr` builds the ask on top of it:

```heather
fn budgeted<A>(fuel: Nat, t: Tac<A>) → Tac<A>             // at most `fuel` requests
fn request_in(g: GoalInfo, fallbacks: List<Tac<Expr>>, fuel: Nat) → Tac<Option<Expr>>
fn request(goal: Handle, fallbacks: List<Tac<Expr>>, fuel: Nat) → Tac<Option<Expr>>
```

`request` tries `Synth` first. If that fails, it runs each fallback at the
goal under `budgeted(fuel, …)`. The budget counts every request the
fallback makes, including the goal questions `focus` answers (the budget
wraps inside `focus` for that reason). A fallback's answer is checked at the
goal (`proves`: infer, then defeq) before it counts, so a fallback that
proves something else is no answer. `None` means skip. This is §6.2's "a
check is a search with a budget" made literal: an LLVM-style check is a
fallback whose budget is small.

## 5. Consuming facts: a compiler proved once over any facts

The compiler must not care where a proof came from or whether there was one.
So its input carries the facts, one per site:

```heather
record Site(len: Nat, bounds: List<Nat>) { ix: Ix, fact: Option<InBounds(len, bounds, ix)> }
record Compiled(p: Prog) { sites: List<Site(p.len, p.bounds)>, same: erase(p.len, p.bounds, sites) = p.reads }
```

- `Site::compile` drops a read's check exactly where `fact` is `Some`.
- `Compiled::runs` proves, once and for any choice of facts, that the
  compiled code computes what the program means, trap included, at every
  argument list the program accepts.
- The pin `same` says the annotated reads are the program's own. It is
  checked by `refl` when the compiled program is built, as a reflected
  `runtime fn`'s pin is (`docs/native/runtime-fn-setups-design.md`).

The generator `compile_reads(p, "name", budget)` (`lib/lang/facts/read_facts.hthr`)
asks for `InBounds` for each read. It passes the exhaustive check at
`budget` as its own fallback, and publishes `fn name() → Compiled(p)`. A read
with a proof gets `read_found(…, proof)`, and a read without one gets
`read_kept(…)`.

Two details of building the generator are worth recording:

- **A goal's arguments are reduced to head normal form before the ask.**
  Evidence rules are prefiltered by the heads of the goal's arguments, and
  the prefilter does not unfold on purpose (`argument_head`). A read written
  `prog_read(p, 2)` would therefore miss a user's lemma about
  `Add(Arg(0), …)`. The generator views the goal and whnfs each argument
  (`in_bounds_goal`). Any generator that asks for facts about code it
  addressed indirectly needs the same step.
- **`Lookup` names functions, not constructors or type formers**, so the
  generator builds terms through small functions (`read_found`,
  `sites_cons`, `CompiledProg`). The interval and `norm_num` tactics do the
  same thing.

## 6. The first fact: `InBounds`

The language (`checked_reads.hthr`) is a program that reads one buffer of
`len` words at index expressions over its arguments (`Const`, `Arg`, `Add`,
truncated `Sub`, `Clamp`), each argument at most its bound, and sums what it
read. Every read is checked, and an out-of-bounds read traps.

`InBounds` has three producers, cheapest first (`in_bounds.hthr`):

1. **A verified analysis.** `Ix::hi` is an upper bound of an index over the
   box, and `hi_sound` proves it once. The producer is the search rule
   `InBounds::of_range`, whose premise evaluates.
2. **User lemmas.** Any `evidence theorem` that concludes `InBounds`. These
   are plain rules, so they are tried before the analysis.
3. **A bounded search.** `InBounds::by_exhaustion` tries every argument list
   in the box by evaluation, and only when the box has at most `budget`
   points. It is proved sound once, so a found fact is one evaluation that
   the kernel repeats. It is the compiler's fallback, not a rule, so the
   compiler sets the budget.

Here is what it does on `lib/_tests/lang/facts/read_facts_tests.hthr`'s
program (buffer of 8 words, `a0 ≤ 7`, `a1 ≤ 3`):

| read | its check | proved by |
|---|---|---|
| `min(a0, 7)` | dropped | range analysis |
| `a1 + 4` | dropped | range analysis |
| `a0 + (7 − a0)` (always 7; the analysis says 14) | dropped | exhaustive check, 32 argument lists |
| `a0 + a1` (reaches 10) | **kept** | nothing; it traps at `(7, 3)`, and so does the compiled code |

At a budget of 16, the third read keeps its check. A read over a box of
101 × 101 points at budget 0 is proved by a user lemma declared beside it.
A program whose every read the analysis proves needs no search at all.

## 7. The second fact: `Unique` over `rt`

Built 2026-11-01, once `rt` had landed (`lib/native/runtime/rt.hthr`).
Code: `lib/lang/facts/unique.hthr` (the fact, its producers, the plan a
lowering consumes) and `lib/lang/facts/write_facts.hthr` (the generator that
asks for it); probes in `lib/_tests/lang/facts/write_facts_tests.hthr`.

**The write.** `rt` gained a byte read and a byte write of a `Bytes` value
at a `Word(64)` index, `Op::Get(cap)` and `Op::Set(cap)`. They mean
`List::byte_at` and `List::with_byte`, which a `runtime fn` writes and the
reflector reads, so the pin stays `refl` (`bump_reflects` in
`lib/_tests/native/runtime/rt_tests.hthr`). Out of range, the read is 0 and
the write changes nothing. `rt` is pure, so a write means a new buffer.
Whether the lowering may build that buffer in the old one's storage is the
fact's question, not the meaning's.

**The statement.** `Unique(p, f, k)`: the `k`th write of function `f` of
program `p` consumes a buffer that nothing reads after the write. "Nothing"
covers the name itself and every name that may share its storage. It is an
equation of a computed verdict, `p.unique_at(f, k) = True`. An equation is
deliberate: the search's computation step (`trivial` at a goal that
reduces to `True`) never answers it, so its producers run in their order
and are not short-circuited by an evaluation of the whole verdict.

The verdict is a liveness analysis over ANF with storage identities:

- Each variable has a set of storage identities. A parameter, or a value a
  node makes, has its own identity, which is its level. A `let` alias, a
  record built from it (`Make`), a field of a record (`Field`), a branch
  result, or a call or fold result has the identities of what it may be.
  Two names can share storage only if their identities meet. A made value
  whose level a later variable repeats only adds sharing that is not there,
  so the analysis can be too cautious but never too bold.
- At a write, the old buffer's class is every variable whose identities
  meet the consumed one's. What runs after the write is the bodies of the
  `let`s it sits inside, innermost first. The write is dead (`ok`) if none
  of those bodies reads a variable of the class. The other arm of a
  branch does not count, and what runs after the branch does.
- **Parameters are owned.** A function owns its buffer parameters: a caller
  moves a buffer into a call and does not read it afterwards. The entry's
  caller, outside the program, is assumed to do the same. So a call, or a
  fold's start (moved into the step), is a consuming use, checked like a
  write. Its buffers must also be pairwise apart, since a callee owning two
  parameters that are one buffer would corrupt the other by writing one,
  and a fold's start must be apart from the buffer it folds. A write whose
  buffer may be a parameter is unique only if the function owns its
  parameters, meaning every call of it in the program moves (`p.owns(f)`).

**Producers**, cheapest first:

1. **The ownership judgment.** `Owned(p)` holds when every consuming use of
   every function in the program is dead. A program that passes it
   publishes the verdict once, as an `evidence theorem`
   (`good_owned` in the probes, by `Owned::by_check`; a runtime setup would
   publish it beside its `judge`). The plain rule `Unique::of_owned({p},
   {f}, {k}, o: Owned(p) := infer)` reads every write's fact off that
   verdict without evaluating anything per site. It is proved once: a
   conjunction over functions and uses gives each write and each callee's
   ownership.
2. **The per-site check.** `Unique::by_check(p, f, k, h)`, where `h` is the
   one write's verdict closed by evaluation. The planner asks for it as its
   fallback when the program fails the judgment as a whole, because some
   other write keeps its old buffer.

**The consumer.** `generate plan_writes(p, f, "name", fallback)` publishes a
`WritePlan(p, f)`: one `WriteSite` per write, in order, each carrying an
`Option<Unique(p, f, k)>`. With a proof the write is `InPlace`; without one
it is `Copied`. Coverage is pinned by `refl`. The probes show the three
routes. `good` publishes its verdict, so its write is in place with the
fallback off. `mixed` contains a function that reads its old buffer, so it
publishes no verdict: its other write is in place only through the
fallback, and the bad write is copied. In `leaky` a caller reads a buffer
after moving it, so the callee's write is copied whatever is asked.

**What is left to the lowering.** The theorem that an in-place write is
correct needs a store: buffers as slots, names mapped to slots, and the
invariant that every live name reads its slot. That store is the runtime
setup's lowering of `Bytes` to a buffer plus a length
(`issues/runtime-default-setup-soundness.md`). Its `sound` takes the plan's
proofs as hypotheses at exactly the sites marked `InPlace`, so it is proved
once for any facts, as `Compiled::runs` was. That theorem, and the
calling-convention half that gives a callee its buffers, are tracked in
[unique-fact](../../issues/unique-fact.md).

## 8. What is open

- **Saying which search rule is cheaper.** Today the order is plain rules,
  then search rules by name. There are three ways out. (a) Exempt from
  Paterson a premise that is closed by computation (`trivial`), so a cheap
  check becomes a plain rule. (b) Order search rules by a declared cost.
  (c) Accept the convention that a fact has at most one search rule and the
  rest are the requester's fallbacks, as here. (c) is enough for now.
- **A `fact` marker**, if facts and ordinary propositions ever need to
  behave differently. Nothing in this round needed one.
- **`InBounds` over `rt` code.** `InBounds` is over a toy language, while
  `Unique` (§7) is over `rt`. Moving `InBounds` to `rt`'s `Get` needs an
  index analysis over `rt` words. A call's facts (Q9, `CallCtx`) would then
  become locals of the request.
- **Contracts across calls** (Q4) are untouched.
- **Cost** was not measured, since this is not a performance round. Each
  request is one resolver search. A search rule costs its tactic, once per
  trial. A fallback costs at most its budget. The exhaustive check is linear
  in the box size, which the budget caps.
