# Simulation between interaction trees

Status: implemented, 2026-10-22 (`lib/std/itree/itree_sim.hthr`, Linux instance
`lib/std/os/linux/linux_trees_sim.hthr`; tests `crates/elab/tests/lib_std_itree_sim.rs`
and `crates/elab/tests/linux_spec.rs`). Issue:
`issues/itree-iter-simulation.md`, milestones `it-library` and
`hih-pl-first-program`. Simulation up to a continuation, the statement kit and
cat's proof (§6, §7): 2026-10-23, `issues/native-source-cat-implements.md`. It builds on the finite library
(`lib/std/itree/itree.hthr`, `lib/std/itree/itree_trace.hthr`) and is what the native
source's proofs against size-free specs go through
(`docs/native/native-effect-source-design.md` §8).

---

## 1. The statement users want

A compiled program meets its source's tree, and the facts users care about
are proved against a spec over other events: `tr`'s source reads with a
size, `tr_spec` reads without one (`lib/native/stream_filter_spec.hthr`). The
statement is about traces:

```
Program::Simulates(E, F, m, ct, p, q) :=
    (tr) → Produces(p, tr) → Valid(ct, tr) → Owes(ct, tr) ∧ Produces(q, along(m, tr))
```

- `m : TraceMap(E, F)` reads a source trace in the spec's events: each
  command names one of `F`, each answer an answer to the image. The
  direction is the trace's, forward from source to spec, so forgetting a
  read's size is a map and needs no inverse.
- `ct : Contract(E)` is what the environment promises (`valid` answers) and
  what the source owes at each call (`owes`). Linux promises an answer no
  longer than the read, and the source owes a read of positive size.

`Program::Refines` is the case `m = id`, `ct = none`
(`refines_of_simulates`), and `Program::Implements` is the case
`m = linux_forget`, `ct = linux` (`implements_of_simulates`), so one library
serves both.

## 2. `Sim`: read off the source

Proving the statement by induction over traces repeats the same case
analysis for every program. `Sim` is a tree-level relation instead, defined
by recursion on the source like `Same` and `Below`:

```
Sim(Ret(x), s)    = SimRet(s, λ y. Q(x, y))       -- next(s) = Exits(y), Q(x, y)
Sim(Tau(t), s)    = Sim(t, s)
Sim(Vis(c, k), s) = SimVis(c, s, λ a v. Sim(k(a), v))
                    -- owes(c), next(s) = Calls(m.cmd(c), k2),
                    -- ∀ a. valid(c, a) → Sim(k(a), k2(m.ans(c, a)))
Sim(Cut, s)       = True
```

The spec is looked at only through `ITree::next`, which skips its silent
steps, so either side may take any number of `Tau`s. A source `Cut` claims
nothing, which is what lets fuel stay out of the statement. The debt `owes`
sits inside `SimVis` rather than beside it: the recursion would otherwise
pass the spec at a changed position outside the record, which the
recursive-call check refuses.

The laws:

- `sim_next`: the spec may be replaced by any tree with the same `next`.
- `sim_below`: a spec that grows (`ITree::Below`) still simulates. A cut in
  the spec is where it ran out of fuel; more fuel keeps every move.
- `sim_bind`: the congruence. `Sim_Q(t, s)` and `Sim_P(h(x), h2(y))` for
  every `Q(x, y)` give `Sim_P(bind(t, h), bind(s, h2))`.
- `sim_trace`: the trace statement, once. Every valid trace of `t` pays its
  debts and, read through `m`, is a trace of `s`.

Proofs about `Sim` match the source and take every hypothesis that depends on
it as an arrow after the match (`λ (h: SimRet…) => …`). A `match` does not
refine the types of earlier parameters, and the elaborator or the kernel
refuses a proof that assumes it does.

## 3. The loop rule

`sim_iter` relates two `iter`s with different state types through
`R : A → A2 → Type`. Its premise is per pass, `PassSim(a, a2)`, one of:

- **a moving pass**: `Sim(body(a), body2(a2))` with outcomes related by
  `Step::Rel(R)` (going round from related states, or leaving with the same
  value);
- **a silent pass**: `Sim(body(a), stay(a2))`, where `stay(a2)` is
  `Ret(Continue(a2))`. The source pass makes no call (the spec offers none)
  and lands in a state related to the spec's unchanged one.

The conclusion is `Sim_eq(iter(n, body, a), iter(n, body2, a2))` at the
*same* fuel `n`. A moving pass consumes one unit on both sides. A silent pass
consumes one on the source side only, so the spec has fuel to spare, and
`sim_below` with `iter_grows` moves it from `iter(n - 1, …)` to
`iter(n, …)`. `simulates_iter` lifts it to programs, and
`Program::implements_iter` is the Linux instance.

## 4. What stays out

- **A pass that is many spec passes**, under `sim_iter`: a source pass
  simulates at most one spec pass there. §6 is the rule for that case.
- **The converse.** `Sim` is partial correctness: a source that is cut early
  simulates anything, so nothing here says the source makes every trace the
  spec makes. No customer needs that direction yet.

## 5. Testing

`lib_std_itree_sim.rs` (the `family_library` binary), on the axes of
`docs/testing-generated-terms.md`:

- the module checks from images, and every item of the kit is named;
- **literal and open**: a countdown loop at an open counter and at `3`;
- **open events**: every test is over an arbitrary `E`;
- **checking position**: each pass's `PassSim` is a `SimRet`/`SimVis`
  record written against the expected type;
- **negative controls**: a spec that leaves with another value, and a source
  call the spec does not make, are refused by conversion;
- a countdown whose passes are all silent refines a loop that leaves at
  once, and a loop that calls simulates its copy call for call.

`linux_spec.rs` runs the countdown through `Program::implements_iter`, with a
spec that leaves with another status as its negative control.

## 6. Up to a continuation

`Sim` relates a source tree to a spec tree that ends where the source ends.
cat's outer pass is a read and then a whole inner loop of writes, and the
spec does that in one pass per call plus one to go back to reading: one
source pass is any number of spec passes, and where the pass returns the
spec is in the middle of its loop. `SimK` says so:

```
SimK(K, Ret(x), s)    = K(x, s)          -- the spec's remaining tree, whatever it is
SimK(K, Tau(t), s)    = SimK(K, t, s)
SimK(K, Vis(c, k), s) = SimVis(c, s, λ a v. SimK(K, k(a), v))
SimK(K, Cut, s)       = True
```

`Sim(Q)` is `SimK` with `K(x, s) = SimRet(s, λ y. Q(x, y))`, by definition,
so every law above is about `SimK` too. The new laws:

- `simk_bind`: `SimK_K(t, s)`, and `SimK_P(h(x), v)` wherever `K(x, v)`,
  give `SimK_P(bind(t, h), s)`. Only the source is bound: the continuation
  carries the spec along.
- `simk_iter`: the loop rule with an invariant `I(k, a, v)` indexed by the
  source's fuel left. From `I(k + 1, a, v)` a pass must reach
  `StepK(I(k), K)`: the invariant one unit down if it goes round, `K` if it
  leaves. Nothing ties the spec's fuel to the source's; the invariant asks
  for enough of it (cat's asks `cat_budget(n, k)`, which grows by `n + 2` a
  pass), and the proof spends it by matching on the spec's fuel where a spec
  pass happens (a fuel of zero contradicts the bound).
- `Program::simulates_at`: simulation at every source fuel `n` against the
  spec at `fuel(n)`.

Nested loops need no rule of their own: the inner loop is `simk_iter` again,
with the rest of the outer pass as its `K`.

**The statement kit** (`lib/native/native_source_sim.hthr`) states these for
the native layer's statements under Linux's map and contract
(`ITree::LinuxSimK`): `Stmt::sim_then` hands the first statement's outcome to
the rest (`Stmt::then_rest`), `sim_branch_true`/`_false` take the side a known
bit picks, `Flow::pass_again`/`pass_leaves` go round or leave by a loop's bit,
and `Stmt::sim_repeat` is `simk_iter` for `Repeat`. A `Compute` block needs no
rule: on an environment whose word file is a literal list
(`native_cat_spec`'s `cat_words`), a block computes by evaluation.

## 7. cat

`lib/native/native_cat_spec.hthr` proves `cat_implements`:
`Program::Implements(cat(c).denote(), tr_spec(λ b => b))` for
`0 < c < 2^63`, and from it `cat_sends`: along every run Linux can give cat
that exits 0, what reached stdout is what was read from stdin.

- **The environment is held concretely.** Its word file is a literal list of
  twenty with the slots cat writes open (`cat_env`), so cat's blocks compute
  by evaluation and what they store stays as the term they computed
  (`cat_wrote`, `cat_read`). The facts are about those terms: a count below
  `2^63` reads back and is nonnegative, a negated errno is negative
  (`bitvec_signed`), the 64-bit add and subtract of the write's bookkeeping do
  not wrap (`bitvec_nat`), and the buffer's span after a write is the spec's
  pending bytes dropped by the count (`List::drop_take`, `drop_drop`).
- **Two invariants.** `CatReading(n, k)` at the outer loop's head: the spec
  is reading with `cat_budget(n, k)` fuel or more. `CatWriting(n, k, j)` at
  the inner loop's head: `left` bytes from `sent` are pending, the spec is
  writing exactly them, with `j + 1` more passes than the rest of the outer
  loop needs. Each records where the spec is by its next move, so the
  spec's silent steps (a pass with nothing pending goes back to reading)
  never need stating.
- **Cost.** Each declaration is a constant number of block evaluations at
  the literal width, independent of the capacity and the fuel; the heaviest
  are the read of some bytes and the arithmetic of a write.

Testing (`crates/elab/tests/native_cat_spec.rs`): the kit is named; a client
instantiates cat at a literal and an open capacity; and a cat that exits 0
after a failed write, with the proof mutated the same way, is refused at the
failed write's exit. `lib_std_itree_sim.rs` checks `simk_iter` on its own: a
loop making two calls a pass against one making one, at twice the fuel,
over open events at an open and a literal state, with a wrong exit refused
by the kernel.
