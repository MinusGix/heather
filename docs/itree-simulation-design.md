# Simulation between interaction trees

Status: implemented, 2026-10-22 (`lib/std/itree_sim.hthr`, Linux instance
`lib/linux_trees_sim.hthr`; tests `crates/elab/tests/lib_std_itree_sim.rs`
and `crates/elab/tests/linux_spec.rs`). Issue:
`issues/itree-iter-simulation.md`, milestones `it-library` and
`hih-pl-first-program`. It builds on the finite library
(`lib/std/itree.hthr`, `lib/std/itree_trace.hthr`) and is what the native
source's proofs against size-free specs go through
(`docs/native-effect-source-design.md` §8).

---

## 1. The statement users want

A compiled program meets its source's tree, and the facts users care about
are proved against a spec over other events: `tr`'s source reads with a
size, `tr_spec` reads without one (`lib/stream_filter_spec.hthr`). The
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

- **A pass that is many spec passes.** A source pass simulates at most one
  spec pass. cat's write loop is an inner `iter` that sends in several
  writes, each a spec pass (`issues/native-source-cat-implements.md`). That
  needs a nested-loop rule, or a lemma folding the inner loop into the outer
  body.
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
