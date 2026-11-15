---
title: Effectful loops without a passes list
status: closed
labels: [language,effects,design]
area: language
milestone: [it-world-loops,nh-effects,lang-sequencing]
created: 2026-11-02
updated: 2026-11-04
---

Effectful loops take a `passes: List<Nat>` and run `for _ in passes`. This is true of `Io::cat` (`lib/_tests/std/os/linux/linux_world_tests.hthr`), `Io::write_all`, and `Io::tac`/`Io::sort` (`lib/native/runtime/line_tools.hthr`). Minus asked what it is really for (PR #394 review, 2026-11-02). It serves two purposes at once, and neither is the program's intent:

- **Totality of the meaning.** "Read until the input ends" terminates only if the world's input is finite, and a `World()` is any function of the history, so nothing bounds it. A `fn` must be total, so the loop needs a bound, and `passes` is that bound.
- **Agreement with the source.** A `Source`'s `Repeat` is `ITree::iter` at a fuel `n` and is cut past it. The surface loop agrees with the compiled one whenever neither is cut (`docs/language/effects-capabilities-design.md` §4).

The program never means "at most `passes.len()` reads". It means "until end of input or a failure". The bound leaks into every signature, every caller, and `runtime fn main`'s argument.

## Options

1. **Fuel in the world.** `Io` carries the budget the way it carries the history: it is only meaning, and nothing at run time. A world-bounded loop (`while io.alive() { … }`, or a `loop` the lowering knows) spends one unit per pass, and running out is a defined outcome of the reading. Programs stop naming a bound. `Io::Reads` quantifies over budgets, and a compiled program's `Repeat` fuel is the same budget. The cost is that `Io` changes shape for every customer, and the budget's outcome needs a name in results.
2. **Loops as coinductive trees.** Write the loop without a bound and make the meaning a tree: [[partial-functions-coinductive]] (`CoTree::rec`), read against a world with fuel only in `Io::against`. This is the honest meaning, but a `mut self` method would then no longer be a plain `Io → Mutated<Io, R>` function, so every theorem about effectful code goes through the tree.
3. **`while … fuel n exhausted e`.** This is the surface already designed (`docs/language/sequencing-surface-design.md` §5.3, not built). It names the bound once per loop rather than threading a list, but the bound is still the program's parameter.
4. **A finite-input world.** Restrict the worlds whose reads terminate by a measure (input left). That would be a `decreases` loop, but it rules out every world that is not a pipe of finite input, which the most-general `World()` was chosen to allow.

Recommendation: 1, with 3 as the spelling for pure loops that genuinely need a bound. This is Minus's call before any customer rewrite; tac, sort, cat, wc and head would all move together.

## Done when

`Io::tac`, `Io::sort`, `Io::cat` and `Io::write_all` take no `passes` and
mean `Io → Partial<Mutated<Io, R>>` (`docs/language/effects-capabilities-design.md`
§4); their probes state the same things, with today's pass counts as the
`Returns` count; a `Source`'s `Repeat` gets a fuel-free denotation over
`CoTree::iter` (bridged to the fuelled one by `iter_refines`), and
`cat_agrees_piped`/`cat_agrees_failing` state `Eutt` through the coinductive
`Io::Reads`.

## Log

- 2026-11-03: Analysed with Minus in a project thread. Beyond the body above: the
  partiality is real (`yes | tac` diverges), so the question is where it
  lives; today's exhaustion reads as a real outcome (`Io::cat` returns 0 when
  its outer `passes` run out, `tac`/`sort` write a truncated read as success);
  `Io::Reads` is an equality at every world, so no fixed-fuel loop tree can
  satisfy it; and `while … fuel` compiles to a counting loop, so it is not the
  answer for loops over a world. **Decided by Minus: the meaning is
  coinductive, `Io → Partial<Mutated<Io, R>>`, and agreement is up to taus**
  (he prefers `Eutt` plus automation to a lockstep-only discipline). Recorded
  in `docs/language/effects-capabilities-design.md` §4 and §7.5. The work is split
  into [[partial-fn-surface]], [[eutt-iteration-and-io-reading]],
  [[codata-up-to-friends-round-2]] (up-to proofs), [[eutt-setoid-rewrite]] and
  [[eutt-tactics]]; this issue stays the customer rewrite, blocked on the first
  two. "Done when" revised to match.
- 2026-11-03: [[partial-fn-surface]] landed: `Partial(B)`, `partial fn`, and `while c { … }` with no measure in any carrier with an `Iterate` instance (CoTree, Partial). What this issue still waits on is [[eutt-iteration-and-io-reading]]; a world-threading loop also needs `Iterate` at state over `Partial` (`Io → Partial<Mutated<Io, R>>`), which is an instance away once that carrier is a constructor the unifier learns.
- 2026-11-04: Done (thread "Give loops over worlds a fuel-free meaning"). `Io::write_all` (now in `linux_world_co`), `Io::tac`, `Io::sort`, `Io::read_lines`, `Io::write_lines` and the test module's `Io::cat` take no `passes` and mean `Io → Partial(Mutated<Io, R>)`, written with `while` and no measure; their probes are `Returns` at a count, with negative controls and a world whose input never ends. A `Source`'s `Repeat` has a fuel-free denotation over `CoTree::iter` (`lib/native/native_source_co.hthr`), the same program as the fuelled one both ways (`Source::tree_co_refines`/`tree_co_refined`, over `ITree::Into`/`CoTree::Onto` in `coitree_bridge`, generalising `iter_refines` to a body that is a family in the fuel). `cat_agrees_piped`/`cat_agrees_failing` state `Eutt` between the source's fuel-free reading and the surface cat at a world (`Io::Reads` at that world). The `while` with no measure has no `break` and does not lower a bind inside a statement arm of its body, so loops stop by a flag and one loop cannot call another (`docs/language/effects-capabilities-design.md` §4.1).
