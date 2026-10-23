# Interaction trees, second round: traces, refinement, a state handler (`it-refinement`)

Date: 2026-10-21. Questions 2 (second half) and 3 of
[interaction-trees-container-model](../issues/interaction-trees-container-model.md),
on top of the core library of [the first round](itree-core-round.md). The
code is [`lib/std/itree/itree_trace.hthr`](../lib/std/itree/itree_trace.hthr) and
[`lib/std/itree/itree_state.hthr`](../lib/std/itree/itree_state.hthr), the client is
[`docs/showcase/itree_refinement_client.hthr`](showcase/itree_refinement_client.hthr),
and the tests are `crates/elab/tests/lib_std_itree_trace.rs`.

The consumer is the native rebuild
([`docs/native-program-logic-design.md`](native-program-logic-design.md) §8,
round S1, `issues/native-linux-spec.md`): `Sim` says the machine produces
exactly a tree's traces, so what S1 needs from here is a trace type, the
relation "this tree can produce this trace", refinement between programs as
families over fuel, and the fact that fuel is not observable.

## What landed

| Piece | Spelling |
| --- | --- |
| Traces | `inductive Trace<R>(E) { TEnd, TRet(r), TCall(c), TAns(c, a: E.Resp(c), rest) }` |
| A tree produces a trace (Fig. 20) | `fn IsTrace(E, t, tr) → Type`, by recursion on `t` into `RetTrace`, `VisTrace`, `CutTrace` |
| Basic facts | `IsTrace::nil` (every tree has the empty trace), `IsTrace::of_same`, `IsTrace::ret_unique`, `IsTrace::bind` with `Trace::seq` |
| The approximation order | `ITree::Below` (a `Cut` is below anything), `below_refl`, `below_bind`, `IsTrace::of_below` |
| Loops and recursion grow with fuel | `ITree::iter_grows`, `ITree::mrec_grows` (via `mrec_layer_below`), `ITree::Grows(E, p)`, `iter_family_grows`, `rec_family_grows` |
| The bridge to `simulate` | `IsTrace::up`, `IsTrace::fuel_monotone`, `record Converges(E, p, tr) { n, h }`, `Converges::at`, `Converges::ret_unique` |
| Refinement | `ITree::Refines(E, p, q)`, `refines_refl`, `refines_trans`, `refines_of_same`, `refines_shift` |
| Programs | `record Program<R>(E) { at, grows }`, `Program::pure`/`iter`/`rec`/`bind`, `Program::Produces`, `Program::Refines` (no fuel in the statement; `refines_of_families` and `families_of_refines` relate it to `ITree::Refines`), `Program::ret_unique` |
| Divergence | `Program::Diverges` (returns at no fuel), `Program::spin`, `Program::spin_diverges`, `Program::pure_not_diverges` |
| State handler (Q3) | `Events::state<S>()` (`Get`, `Put(s)`), `ITree::run_state`, `ITree::run_state_bind` |
| World threading | `ITree::returned`, `ITree::thread(t, s) → Option<Pair<S, R>>`, `ITree::returned_of_trace` |

The client builds a console program's trace answer by answer, shows it never
writes before it reads, proves a countdown loop refines itself at any larger
fuel, and threads a counter: `thread(twice(), 5) = Some(Pair(7, 11))` by
`refl`, and at an open state in the tests.

## Decisions

**A trace says how it ends.** `TEnd` is a prefix stopped anywhere, `TCall(c)`
a command issued and not yet answered, `TRet(r)` the return. Prefix closure is
built in (`IsTrace::nil`, and `Prefix` at every `Vis`), so the trace set of a
tree is the paper's Fig. 20 set together with its prefixes. That is the shape
`Sim` needs: the machine's partial runs are prefixes, and a pending call is
what a machine blocked in a syscall has produced.

**`IsTrace` is computed from the tree, and its cases are inductives with
value parameters.** As with `Same`, each case reads the left tree and says
what the trace is: `RetTrace(E, r, tr)` (`tr = TEnd` or `tr = TRet(r)`),
`VisTrace(E, c, tr, S)` (a prefix, the call pending, or an answer `a` and a
trace of `k(a)`), `CutTrace(E, tr)` (`tr = TEnd` only). The command is the
tree's own, so nothing is transported between response types. A `Cut`
produces only the empty prefix: a tree cut at fuel claims nothing past the
cut, which is what makes fuel safe to quantify over.

**A program is a family over fuel, and refinement quantifies over it.**
`Refines(E, p, q)` says every trace `p` produces at some fuel, `q` produces at
some fuel of its own (`Converges`). For deterministic trees this inclusion is
the weak equivalence the paper's §7 relates to eutt, so the depth-indexed
bisimilarity of the Coq probe is not needed as a separate relation: the first
round's `Same` is structural equality of finite trees, and fuel does the index's
job one level up, across the family. Trees that are the `Same` at every fuel
refine each other (`refines_of_same`), so round 1's laws carry over.

**Fuel is not observable.** `Below(E, t, u)` is `Same` with one more freedom,
a `Cut` below anything. `iter` grows with fuel (`iter_grows`), a family that
grows is `Grows`, and along a growing family every trace seen at some fuel is
seen at every larger fuel (`fuel_monotone`). That is `simulate`'s
`fuel_monotone` (`docs/ir-simulate-design.md` §6), and `Converges` is its
`converges` with the bound hidden; `Converges::at` raises the bound, and
`Converges::ret_unique` says a growing program returns at most one value,
whatever fuel each return was seen at. `refines_shift` is the payoff: a
family refines itself shifted by any amount of fuel.

**A program carries its growth, so fuel stays inside the definitions.**
Fuel has the usual hazards: running out confused with a result, specs that
name an amount, monotonicity re-proved at every use, and divergence that
cannot be told from too little fuel. The first cannot happen here, since
`Cut` is a leaf of its own and returns nothing. For the others, `Program<R>(E)`
packs the family with its `Grows` proof, so a family that uses fuel in any
other way (`if n > 5 then Ret(1) else Ret(2)`) is not a program. Growth is
proved once per combinator (`pure`, `iter`, `rec` through `mrec_grows`, and
`bind` through `below_bind`), and the statements about programs name no fuel:
`Produces(p, tr)` is "at some fuel", and `Program::Refines(p, q)` is plain trace
inclusion, equivalent to the fuel-indexed `ITree::Refines` of the families.
`Diverges(p)` says `p` returns at no fuel at all. For programs built from
`iter` and `rec`, fuel is the only source of `Cut`, so that is divergence and
not missing fuel, and it is proved by induction on the fuel
(`spin_diverges`). A `Cut` written by hand claims nothing, so a program built
from one "diverges" vacuously; that is the honest reading of a tree that
claims nothing.

**Where fuel is weaker.** Safety, refinement and termination of deterministic
programs are what this states well, and they are S1's job. Liveness over
unbounded interaction ("every request is eventually answered" by a server
that never stops) can only be written as a nested "every prefix, some fuel
further" statement, and fairness and concurrency are out of reach; those are
the customers that kernel coinduction waits on
([interaction-trees-container-model](../issues/interaction-trees-container-model.md)).
Trace inclusion is eutt only for deterministic trees, so choice trees reopen
the question, as Q1 records.

**`bind`'s traces are sequenced traces.** `Trace::seq(tr, k)` continues a
trace past its return; `IsTrace::bind` says a trace of `t` continued by traces
of `h` at each return value is a trace of `bind(t, h)`. This is the
direction a compiler proof composes in (a statement's trace, then the rest's).
The converse, splitting a trace of `bind(t, h)`, is not proved yet; S1 can add
it when a proof needs it.

**The state handler is world threading.** `run_state` answers `Get` and
`Put(s)` by passing a state value through the tree and leaves the other
events in place: a tree over `State + E` becomes a tree over `E` returning
the final state with the result. With no other events (`Events::none()`) a
tree only steps, returns or is cut, and `thread(t, s)` reads the result off as
an `Option`. `run_state_bind` (a monad morphism, up to `Same`) is Q3's
answer: interpreting state events *is* threading a world through the program,
and it composes with sequencing, so the two leanings of
[effects-direction](../issues/effects-direction.md) meet rather than compete.
`returned_of_trace` says the threaded value is the one the traces return.

**Small lemmas over the uncomputed cases.** A proof that matches on a
`VisTrace` or `RetTrace` hypothesis inside a recursion over the tree pays for
the computed motive in every arm. Stating the case analysis once, over the
inductive with an abstract continuation relation (`VisTrace::map`,
`VisTrace::seq`, `RetTrace::returns`, `VisTrace::never_returns`,
`CutTrace::ended`), and calling it from the recursion took `ret_unique` from
the module's most expensive item to a cheap one and roughly halved `of_same`,
`of_below` and `IsTrace::bind`. Likewise a `Same`/`Below` congruence states
the right tree's equation with `cong` instead of rewriting the whole relation
with `j` (`same_bind` in `itree.hthr`, `below_bind`).

## Costs

While this round was written, tier 2 spelled its leaf predicate inline at
every use of `ITree<R>(E)` and `Trace<R>(E)`, and the three modules with the
core library cost most of a test process's CPU rail cold, the kernel gate
dominating. The restructuring above cut the trace module by about 40%. Then
[#98](https://github.com/MinusGix/heather/pull/98) named the leaf predicate as
a generated definition, and the same closure became cheaper by more than an
order of magnitude, every count column falling with it: the induction proofs
are now ordinary items, the most expensive about a second. No staged warmup
or split test target is needed.

## Frictions met

- A `match` does not refine earlier hypotheses, so a proof that needs a
  hypothesis at the matched constructor takes it after `:` in the result
  type and binds it with `λ` in each arm (`ret_unique`, `returned_of_trace`);
  a case split on a sum command returns a function (`state_vis`), as
  `mrec_vis` did in round 1.
- A trace constructor in a type argument (`RetTrace<R>(E, r, TRet(r))`) is
  fine, but in an argument position whose type still mentions an implicit
  it needs the element type (`CutTrace::ended<R>(…, TRet(r), w)`).
- Recursive calls inside a `j` argument or a type argument were not seen by
  IH generalization and are hoisted into `let ih`
  ([ih-generalization-misses-call-under-j](../issues/ih-generalization-misses-call-under-j.md),
  since fixed for `j`; the hoists stay because they also name the IH's type).
