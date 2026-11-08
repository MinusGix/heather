---
title: Build the uniqueness-threaded effects surface over the program builder
status: open
labels: [language,effects,native,frontend]
area: language
created: 2026-10-28
updated: 2026-11-08
milestone: [nh-effects, lang-sequencing]
---

The decided effects story ([[effects-direction]], 2026-10-21) is a
uniqueness-threaded surface that denotes interaction trees. Nothing builds it
yet: effectful programs are written in the program builder
(`lib/native/native_build.hthr`, [[native-source-builder]]) or as a `Source`
directly. This is the language round that gives them a front end.

## Scope

- Effectful code in ordinary Heather syntax over capabilities (`uniq Fd`,
  `uniq Buf`), elaborating locally into the builder or straight into
  `Source` (`docs/native-effect-source-design.md` §9): a `let` of pure
  expressions becomes a `Pure` leaf, `io.read(fd, buf)` a `Call`,
  `loop`/`while` a `Loop`, `for` and structural recursion FunctionIR's
  bounded loop.
- The pure reading users reason with (world threading) agrees with `denote`
  construct by construct, proved once (`ITree::run_state_bind`'s statement).
- The assignment glyph. `=` is propositional equality, so assignment is
  `:=` (held free for this by `docs/let-and-blocks-design.md` §3.1).
  [[warn-bare-eq-no-effect]] waits on it.
- Interleaved statements in a block (`let a = …; f(x); g(a)`), deferred here
  by `docs/let-and-blocks-design.md` §4.5: the form means something once a
  statement can have an effect.
- Users never write monadic types or prove against a CPS elaboration target
  ([[effects-direction]]'s "avoid").

## What it assumes from elsewhere

- **[[effects-direction]]** owns the decision. Assumed here: only that the
  surface is uniqueness threading denoting trees.
- **[[native-source-builder]]** owns the builder this surface targets.
  Assumed here: only that the builder is the surface's back half
  (`docs/native-real-programs-plan.md` §3.3).

## Log

- 2026-10-31: 2026-10-31: Round R6 of docs/compiler-milestones-proposal.md (§4.2 N3, milestone nh-effects): written with the sequencing surface ([[sequencing-surface-design]]) as a runtime fn under the default setup ([[runtime-fn-default-setup]]). Done when cat FILE…, wc and head -n are rewritten in it and pass the same GNU tests, and their builder versions are deleted. Also owns byte and string literals in programs and [[feature-implicit-module-dependencies]] for program files.
- 2026-10-31: 2026-10-31: docs/sequencing-surface-design.md §8: effects use layer 2 (let mut + mut self methods: a capability is a mutable local, and Fd::read(mut self fd, …) returns the pair and reassigns), not layer 1 over ITree, which would be the monadic surface effects-direction rules out. mut self lands in R3a ([[pure-imperative-statements]]); this round owns its effectful customers, the denotation agreement and linearity as a setup judgment.
- 2026-10-31: 2026-10-31: `docs/runtime-fn-setups-design.md` §6.1, §8: the default setup's `sound` is where the effectful agreement (`Implements(c.denote(args), p.tree(args))`) is proved once; `rt` gains capability types and an `Invoke` node, the lowering emits `Source` directly (pure runs as `Compute` leaves through N1), and capability linearity is a clause of the default judgment.
- 2026-11-02: 2026-11-02: First slice built (docs/effects-capabilities-design.md). The capability is one `Io` (lib/std/os/linux/linux_world.hthr): a world, a function from the history of exchanges to the answer to the next call (every deterministic environment), and the history itself (how a theorem states output, `Io::sent`). Not `uniq Fd` per descriptor (interleaving across descriptors is observable), not codata (the history would be hidden), not a class-generic world (a type parameter on every signature). `mut self` methods are built as a general language feature: the result is a prelude record `Mutated<S, R>`; the parser marks method calls on mutable locals as candidates, the declaring block claims them, and the elaborator binds the value and rebinds the receiver when the call's type is `Mutated`. The tree reading `Io::against` and agreement `Io::Reads` with `Io::reads_bind` (run_state_bind's statement at this handler, an equation) are proved once. `Io::cat` written in the surface agrees with native_cat's hand-built Source, history and all, read against a piped world by refl (lib/_tests/std/os/linux/linux_world_tests.hthr). Left, in order (design §6): rt capability types and `Invoke`; rt to Source with sound as `Io::Reads`; the loop lemma; linearity in the default judgment; `runtime fn main`; then cat/wc/head rewritten and the builder versions deleted. Follow-up filed: [[mut-self-call-on-immutable-refusal]].
- 2026-11-02: 2026-11-02: slice 2, rt capability layer: ETm (Pure/Let/Invoke) over pure Tm with word-level Effects (Reads/Writes/Opens/Closes) in lib/native/runtime/rt_io.hthr; the capability is the threaded world, not an rt Ty, so linearity holds by construction (design §8). Pin echo_reflects by refl against surface Io::echo_once; stale-buffer negative control. Next: the reflector reading the io chain into Invokes (§8.3).
- 2026-11-04: slice 3, the effectful reflector (design §8.3): lib/native/runtime/rt_io_reflect.hthr reads a `mut self` body over `Io` into an `ETm` by walking the world chain from the result back to `io`; each call's operands are pure `rt` with `Let`s, then its `Invoke`; `.value`/`.value.buf`/`.value.result` read the `Invoke`-bound variables (rt_reflect's `Known` gains an optional `IoKnown`; mut-self calls are pointer-shared, so answers key on handles, copies confirmed by `Defeq`). Linearity is the reflector's refusals at the call: the world as a value, the world after a call as a value, an answer of a call off the chain (a copied `io`, a dropped world after), an unknown method, a world through a branch. Named constants (`Io::stdin()`) reflect as their literal. Probes: `reflects_io_as` for echo_once, a three-call open/read/close, a call-free method, all pinned by `refl`, and five refusals. Left (design §6): rt to Source with `sound` as `Io::Reads`; branches over the world (§8.4) and loops (`ERepeat`); `runtime fn main`; the customers.
- 2026-11-05: gardener: cites a file it shares with [[runtime-fn-setups-design]] (`lib/native/native_build.hthr`).
- 2026-11-08: slice 4, rt to Source for computations with no loop (design §8.5): `ETm::lower` (lib/native/runtime/rt_io_lower.hthr) lowers pure values through `Tm::lower` plus a move to a fresh word, `Invoke`s to `Invoke` statements over a variable layout (`Loc`: word, buffer, or `Gone` once a read wrote over the buffer, which the lowering refuses). `Stmt::thread`/`Stmt::reads_thread` (lib/native/native_source_io.hthr) give straight statements a world-threading meaning their tree reads as. `ETm::lower_sound` by induction over `ETm`, and `ETm::lower_reads`: the lowered tree reads as `ETm::sem` at every world (`Io::Reads`). rt_lower: `Ty::Holds`/`FlatHolds` at `Bytes` are now `True`. Probes: echo lowered, run at a piped world, and its tree read as the surface `Io::echo_lowered`; refusals for a stale buffer and a buffer bound by a pure `Let`. Left (design §6): branches over the world and `ERepeat` loops; `runtime fn main` publishing the lowered Source; the customers.
- 2026-11-08: slice 5, loops over the world (design §8.6): `ELoop` (lib/native/runtime/rt_io_loop.hthr) chains loop-free computations and `while` loops whose state is the whole environment, each pass rebinding every variable to one of the body's end context; meaning in `Partial` as `if c { do body while c }` (`Io::iterate`). Lowered to `Repeat`: body, moves of each word back to its place (a buffer must end in its own buffer, so a stale buffer is refused), condition again into the flag. `ELoop::lower_sound` and `ELoop::lower_reads` (`Io::Reads` against the meaning). Supporting: `Stmt::run`/`reads_run` (every statement as world threading in `Partial`, tree read as it), `Io::iterate_rel` (loops that go round together agree, by direct corecursion), `ETm::sem_end` and the loop-free lowering keeping the end environment. Probe: an echo-until-EOF loop runs "hiyo" at a piped world as its surface `while` does. Left: branches over the world (`EIf`); the reflector for `while` and the bridge to `ELoop::sem`; `runtime fn main`; the customers.
